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

module Controller ( controllerStart
                  , controllerCLI) where

import qualified Database.PostgreSQL.Simple as PG
import qualified Data.ByteString.Char8 as BS
import Data.List
import Data.Maybe
import Control.Exception
import Control.Monad
import "daemons" System.Daemon
import Pipes
import Control.Pipe.Serialize ( serializer, deserializer )

import Util
import Syntax
import Refine
import NS
import Relation
import Name
import Type
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

data Violation = Violation Relation Constraint SMT.Assignment

instance Show Violation where
    show (Violation rel c asn) = "row " ++ show asn ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerStart :: String -> Int -> Refine -> IO ()
controllerStart dbname port r = do
    let dopts = DaemonOptions{ daemonPort           = port
                             , daemonPidFile        = InHome
                             , printOnDaemonStarted = True}
    ensureDaemonWithHandlerRunning "cocoon" dopts (controllerLoop dbname r)

controllerLoop :: String -> Refine -> Producer BS.ByteString IO () -> Consumer BS.ByteString IO () -> IO ()
controllerLoop dbname r prod cons = 
    -- serializer and deserializer pipes below are necessary to avoid stalling the pipeline
    -- due to lazy reading
    runEffect (cons <-< serializer <-< commandHandler (ControllerDisconnected dbname r) <-< deserializer <-< prod)

commandHandler :: ControllerState -> Pipe BS.ByteString BS.ByteString IO ()
commandHandler state = do
    cmd <- await
    -- TODO: parse command
    (state', response) <- lift $
        (case cmd of
             "connect"    -> connect state
             "disconnect" -> disconnect state
             --"status"     -> 
             _            -> return (state, "Invalid command"))
        `catch` (\e -> return (state, show (e::SomeException)))
    yield $ BS.pack response
    commandHandler state'

type Action = ControllerState -> IO (ControllerState, String)

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

controllerCLI :: Int -> IO ()
controllerCLI port = do
    resp::(Maybe BS.ByteString) <- runClient "localhost" port (BS.pack "connect")
    case resp of
         Nothing -> fail $ "Unable to connect to cocoon controller.  Is the controller running on port " ++ show port ++ "?"
         Just r  -> putStrLn $ "Response from controller: " ++ BS.unpack r 
    resp::(Maybe BS.ByteString) <- runClient "localhost" port (BS.pack "disconnect")
    case resp of
         Nothing -> fail $ "Unable to connect to cocoon controller.  Is the controller running on port " ++ show port ++ "?"
         Just r  -> putStrLn $ "Response from controller: " ++ BS.unpack r 


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


