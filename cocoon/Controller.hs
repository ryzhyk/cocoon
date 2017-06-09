{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}

{-# LANGUAGE RecordWildCards, LambdaCase, ScopedTypeVariables, ImplicitParams, OverloadedStrings, PackageImports #-}

module Controller (controllerStart) where

import qualified Database.PostgreSQL.Simple as PG
import qualified Data.ByteString.Char8 as BS
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Control.Exception
import Control.Monad
import "daemons" System.Daemon
import Pipes
import Control.Pipe.Serialize ( serializer, deserializer )
import GHC.IO.Handle
import System.IO
import qualified Control.Concurrent.Lock as L
import Data.IORef
import Text.Parsec
import Eval

import Util
import Syntax
import Refine
import NS
import Relation
import Name
import Type
import Parse
import Validate
import qualified SQL
import qualified SMT.Datalog   as DL
import qualified SMT.Z3Datalog as DL
import qualified SMT           as SMT
import qualified SMT.SMTSolver as SMT


data ControllerState = ControllerDisconnected { ctlDBName       :: String
                                              , ctlRefine       :: Refine
                                              }
                     | ControllerConnected    { ctlDBName       :: String
                                              , ctlRefine       :: Refine
                                              , ctlDL           :: DL.Session
                                              , ctlConstraints  :: [(Relation, [DL.Relation])]
                                              , ctlDB           :: PG.Connection
                                              }

type DaemonState = (Maybe Handle, ControllerState)

data Violation = Violation Relation Constraint SMT.Assignment

instance Show Violation where
    show (Violation rel c asn) = "row " ++ show asn ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerStart :: String -> FilePath -> Int -> Refine -> IO ()
controllerStart dbname logfile port r = do
    let dopts = DaemonOptions{ daemonPort           = port
                             , daemonPidFile        = InHome
                             , printOnDaemonStarted = True}
    lock <- L.new
    ref <- newIORef (Nothing, ControllerDisconnected dbname r)
    ensureDaemonWithHandlerRunning "cocoon" dopts (controllerLoop lock ref logfile)

controllerLoop :: L.Lock -> IORef DaemonState -> FilePath -> Producer BS.ByteString IO () -> Consumer BS.ByteString IO () -> IO ()
controllerLoop lock ref logfile prod cons = do
    L.with lock $ do
        (mhlog, state) <- readIORef ref
        hlog <- case mhlog of 
                     Nothing -> do h <- openFile logfile WriteMode
                                   hSetBuffering h NoBuffering
                                   hDuplicateTo h stdout
                                   hDuplicateTo h stderr
                                   return h
                     Just h  -> return h
        writeIORef ref (Just hlog, state)
        -- serializer and deserializer pipes below are necessary to avoid stalling the pipeline
        -- due to lazy reading
        runEffect (cons <-< serializer <-< commandHandler ref <-< deserializer <-< prod)

commandHandler :: IORef DaemonState -> Pipe BS.ByteString BS.ByteString IO ()
commandHandler ref = do
    cmdline <- await
    (mh, state) <- lift $ readIORef ref
    (state', response) <- lift $ (do
        cmd <- case parse cmdGrammar "" (BS.unpack cmdline) of
                    Left  e -> error $ show e
                    Right c -> return c
        case cmd of
             Left c  -> execCommand c state
             Right e -> execExpr e state)
         `catch` (\e -> return (state, show (e::SomeException)))
    yield $ BS.pack response
    lift $ writeIORef ref (mh, state')

type Action = ControllerState -> IO (ControllerState, String)

execCommand :: [String] -> Action
execCommand ["connect"]          s       = connect s
execCommand ("connect":_)        _       = error "connect does not take arguments" 
execCommand ["disconnect"]       s       = disconnect s
execCommand ("disconnect":_)     _       = error "disconnect does not take arguments"
execCommand _ ControllerDisconnected{}   = error "command not available in disconnected state"
execCommand ("show":as)          s       = showcmd as s
execCommand _                    _       = error "invalid command"

execExpr :: Expr -> Action
execExpr e s@ControllerConnected{..} =
    case exprValidate ctlRefine CtxRefine e of
         Left er -> error er
         Right _ -> do (val ,_) <- evalExpr ctlRefine CtxRefine M.empty ctlDL e
                       return (s, intercalate ",\n" $ map show val)
execExpr _ _ = error "execExpr called in disconnected state"
                    

showcmd :: [String] -> Action
showcmd as s@ControllerConnected{..} = do
    res <- case as of
                ["tables"]    -> return $ intercalate "\n" $ map name tables
                ["views"]     -> return $ intercalate "\n" $ map name views
                ["relations"] -> return $ intercalate "\n" $ map name rels
                [t]           -> maybe (error $ "unknown relation " ++ t)
                                       (return . show)
                                       (find ((==t) . name) rels)
                _             -> error "unknown command"
    return (s, res)
    where 
    rels = refineRels ctlRefine
    tables = filter (not . relIsView) rels
    views = filter relIsView rels
showcmd _ _ = error $ "Controller.showcmd called in disconnected state"

connect :: Action
connect ControllerDisconnected{..} = do
    let ?r = ctlRefine
    db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ ctlDBName
    (do --runEffect $ lift (return $ BS.pack "Connected to database") >~ cons
        (dl, constr) <- startDLSession
        (do let ?s = ControllerConnected ctlDBName ctlRefine dl constr db
            populateDB
            return (?s, "Connected"))
         `catch` \e -> do
             closeDLSession dl
             throw (e::SomeException))
     `catch` \e -> do 
         PG.close db
         throw (e::SomeException)
connect ControllerConnected{} = throw $ AssertionFailed "already connected"

-- This is the only way to transition to disconnected state.
-- Performs correct cleanup
disconnect :: Action
disconnect ControllerConnected{..} = do
    closeDLSession ctlDL
    PG.close ctlDB
    return $ (ControllerDisconnected ctlDBName ctlRefine , "Disconnected")
disconnect ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

startDLSession :: (?r::Refine) => IO (DL.Session, [(Relation, [DL.Relation])])
startDLSession = do
    let rels = refineRelsSorted ?r
    let funcs = map (getFunc ?r) $ nub $ concatMap (relFuncsRec ?r) rels
    let funcs' = map SMT.func2SMT funcs
    let structs = map (\t -> SMT.struct2SMT (name t) $ typeCons $ fromJust $ tdefType t)
                  $ nub $ map (structTypeDef ?r . typ' ?r) 
                  $ filter (\case 
                             TStruct _ _ -> True
                             _           -> False) 
                  $ typeSort ?r $ nub $ concatMap (relTypes ?r) rels
    let dlrels = zip rels $ map SMT.rel2DL rels
    let (allrels, allrules) = unzip $ concatMap ( (\(mrel,crels) -> mrel:(concat crels)) . snd) dlrels
    dl@DL.Session{..} <- (DL.newSession DL.z3DatalogEngine) structs funcs' allrels
    mapM_ addRule $ concat allrules
    return (dl, map (mapSnd (map (fst . last) . snd)) dlrels)


closeDLSession :: DL.Session -> IO ()
closeDLSession dl = DL.closeSession dl

populateDB :: (?r::Refine, ?s::ControllerState) => IO ()
populateDB = do 
    PG.withTransaction (ctlDB ?s) $ readDB
    validateConstraints
    

validateConstraints :: (?s::ControllerState) => IO ()
validateConstraints = do
    violations <- checkConstraints 
    let e = concatMap (("Integrity violation: " ++) . show) violations
    unless (null e) $ throw $ AssertionFailed e

checkConstraints :: (?s::ControllerState) => IO [Violation]
checkConstraints = 
    (liftM concat) 
    $ mapM (\(rel, dlrels) -> do assigns <- mapM (DL.enumRelation (ctlDL ?s) . name) dlrels
                                 return $ concatMap (\(asns, constr) -> map (Violation rel constr) asns) 
                                        $ filter (not . null . fst)
                                        $ zip assigns (relConstraints rel)) 
    $ ctlConstraints ?s
   
readDB :: (?r::Refine, ?s::ControllerState) => IO ()
readDB = mapM_ (\rel -> do rows <- SQL.readTable (ctlDB ?s) rel
                           mapM_ (\(idx, args) -> (DL.addGroundRule $ ctlDL ?s) 
                                                  $ DL.GroundRule (name rel) (map (SMT.expr2SMT CtxRefine) args) idx) rows) 
         $ filter (not . relIsView) $ refineRels ?r


-- :validate
--
--insert relname (<val1>, <val2>)
--the (p in <relation> | <cond>) p
--
--every request is a transaction
