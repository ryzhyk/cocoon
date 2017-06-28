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
import Name
import Parse
import Validate
import qualified SQL
import qualified Datalog.Datalog         as DL
import qualified Datalog.DataflogSession as DL
import qualified Datalog                 as DL
import qualified SMT                     as SMT


data ControllerState = ControllerDisconnected { ctlDBName       :: String
                                              , ctlDFPath       :: FilePath
                                              , ctlRefine       :: Refine
                                              }
                     | ControllerConnected    { ctlDBName       :: String
                                              , ctlDFPath       :: FilePath
                                              , ctlRefine       :: Refine
                                              , ctlDL           :: DL.Session
                                              , ctlConstraints  :: [(Relation, [DL.Relation])]
                                              , ctlDB           :: PG.Connection
                                              , ctlXaction      :: Bool
                                              }

type DaemonState = (Maybe Handle, ControllerState)

data Violation = Violation Relation Constraint DL.Fact

instance Show Violation where
    show (Violation rel c f) = "row " ++ show f ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerStart :: String -> FilePath -> FilePath -> Int -> Refine -> IO ()
controllerStart dbname dfpath logfile port r = do
    let dopts = DaemonOptions{ daemonPort           = port
                             , daemonPidFile        = InHome
                             , printOnDaemonStarted = True}
    lock <- L.new
    ref <- newIORef (Nothing, ControllerDisconnected dbname dfpath r)
    ensureDaemonWithHandlerRunning "cocoon" dopts (controllerLoop lock ref logfile)

controllerLoop :: L.Lock -> IORef DaemonState -> FilePath -> Producer BS.ByteString IO () -> Consumer BS.ByteString IO () -> IO ()
controllerLoop lock ref logfile prod cons = do
    L.with lock $ do
        (mhlog, state) <- readIORef ref
        hlog <- case mhlog of 
                     Nothing -> do h <- openFile logfile WriteMode
                                   hDuplicateTo h stdout
                                   hDuplicateTo h stderr
                                   hSetBuffering stdout NoBuffering
                                   hSetBuffering stderr NoBuffering
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
execCommand ["start"]            s       = start s
execCommand ("start":_)          _       = error "start does not take arguments"
execCommand ["rollback"]         s       = rollback s
execCommand ("rollback":_)       _       = error "rollback does not take arguments"
execCommand ["commit"]           s       = commit s
execCommand ("commit":_)         _       = error "commit does not take arguments"
execCommand _ ControllerDisconnected{}   = error "command not available in disconnected state"
execCommand ("show":as)          s       = showcmd as s
execCommand _                    _       = error "invalid command"

execExpr :: Expr -> Action
execExpr e s@ControllerConnected{..} =
    case exprValidate ctlRefine CtxCLI e of
         Left er -> error er
         Right _ -> do (val ,_) <- evalExpr ctlRefine CtxRefine M.empty ctlDL e
                       return (s, intercalate ",\n" $ map show val)
execExpr _ _ = error "execExpr called in disconnected state"
                    

showcmd :: [String] -> Action
showcmd as s@ControllerConnected{..} = do
    res <- case as of
                ["tables"]    -> return $ intercalate "\n" $ map relname tables
                ["views"]     -> return $ intercalate "\n" $ map relname views
                ["relations"] -> return $ intercalate "\n" $ map relname rels
                [t]           -> maybe (error $ "unknown relation " ++ t)
                                       (return . show)
                                       (find ((==t) . name) rels)
                _             -> error "unknown command"
    return (s, res)
    where 
    relname rel@Relation{..} = (if' relMutable "state " "") ++ (if' (relIsView rel) "view" "table") ++ " " ++ relName
    rels = refineRels ctlRefine
    tables = filter (not . relIsView) rels
    views = filter relIsView rels
showcmd _ _ = error $ "Controller.showcmd called in disconnected state"

connect :: Action
connect ControllerDisconnected{..} = do
    let ?r = ctlRefine
    db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ ctlDBName
    (do --runEffect $ lift (return $ BS.pack "Connected to database") >~ cons
        (dl, constr) <- startDLSession ctlDFPath
        (do let ?s = ControllerConnected ctlDBName ctlDFPath ctlRefine dl constr db False
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
    (when ctlXaction $ DL.rollback ctlDL) `catch` \e -> error $ "Rollback failed: " ++ show (e :: SomeException)
    (closeDLSession ctlDL) `catch` \e -> error $ "failed to close Datalog session: " ++ show (e :: SomeException)
    PG.close ctlDB `catch` \e -> error $ "DB disconnect error: " ++ show (e::SomeException)
    return $ (ControllerDisconnected ctlDBName ctlDFPath ctlRefine , "Disconnected")
disconnect ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

start :: Action
start s@ControllerConnected{..} | not ctlXaction = do
    DL.start ctlDL
    return $ (s{ctlXaction = True}, "ok")
                                | otherwise = error "Transaction already in progress"
start ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

rollback :: Action
rollback s@ControllerConnected{..} | ctlXaction = do
    DL.rollback ctlDL
    return $ (s{ctlXaction = False}, "ok")
                                   | otherwise = error "No transaction in progress"
rollback ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

commit :: Action
commit s@ControllerConnected{..} | ctlXaction = do
    DL.commit ctlDL
    return $ (s{ctlXaction = False}, "ok")
                                 | otherwise = error "No transaction in progress"
commit ControllerDisconnected{} = throw $ AssertionFailed "no active connection"



startDLSession :: (?r::Refine) => FilePath -> IO (DL.Session, [(Relation, [DL.Relation])])
startDLSession dfpath = do
    let (structs, funcs, rels) = DL.refine2DL ?r
    let (allrels, _) = unzip $ concatMap ( (\(mrel,crels) -> mrel:(concat crels)) . snd) rels
    dl <- DL.newSession dfpath structs funcs allrels
    return (dl, map (mapSnd (map (fst . last) . snd)) rels)

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
    $ mapM (\(rel, dlrels) -> do facts <- mapM (DL.enumRelation (ctlDL ?s) . name) dlrels
                                 return $ concatMap (\(fs, constr) -> map (Violation rel constr) fs) 
                                        $ filter (not . null . fst)
                                        $ zip facts (relConstraints rel)) 
    $ ctlConstraints ?s
   
readDB :: (?r::Refine, ?s::ControllerState) => IO ()
readDB = mapM_ (\rel -> do rows <- SQL.readTable (ctlDB ?s) rel
                           mapM_ (\args -> (DL.addFact $ ctlDL ?s) 
                                           $ DL.Fact (name rel) (map (SMT.expr2SMT CtxRefine) args)) rows) 
         $ filter (not . relIsView) $ refineRels ?r


-- :validate
--
--insert relname (<val1>, <val2>)
--the (p in <relation> | <cond>) p
--
--every request is a transaction
