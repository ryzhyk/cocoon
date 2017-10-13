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
import qualified Data.ByteString.Char8      as BS
import qualified Data.Map.Lazy              as M
import qualified Data.Set                   as S
import Data.List
import Data.Maybe
import Control.Exception
import Control.Monad
import "daemons" System.Daemon
import Pipes
import Control.Pipe.Serialize ( serializer, deserializer )
import GHC.IO.Handle
import System.IO
import qualified Control.Concurrent      as T
import qualified Control.Concurrent.Lock as L
import qualified Control.Concurrent.MVar as MV
import Data.IORef
import Text.Parsec
import Eval

import Util
import Syntax
import Name
import Parse
import Validate
import Relation
import Refine
import Port
import Switch
import NS
import Backend
import qualified SQL
import qualified Datalog.Datalog         as DL
import qualified Datalog.DataflogSession as DL
import qualified Datalog                 as DL
import qualified SMT                     as SMT
import qualified SMT.SMTSolver           as SMT
import qualified IR.IR                   as IR
import qualified IR.Compile2IR           as IR

-- Messages sent by the primary controller thread to the
-- synchronization thread.
data Msg = MsgSync       -- database changed -- reconfigure the switches
         | MsgTerminate  -- disconnecting -- terminate

data ControllerState p = ControllerDisconnected { ctlWorkDir        :: FilePath
                                                , ctlBackend        :: Backend p
                                                , ctlDBName         :: String
                                                , ctlDFPath         :: FilePath
                                                , ctlRefine         :: Refine
                                                , ctlIR             :: p
                                                , ctlXactionLock    :: L.Lock
                                                , ctlBackendRunning :: Bool
                                                }
                       | ControllerConnected    { ctlWorkDir        :: FilePath 
                                                , ctlBackend        :: Backend p
                                                , ctlDBName         :: String
                                                , ctlDFPath         :: FilePath
                                                , ctlRefine         :: Refine
                                                , ctlIR             :: p
                                                , ctlDL             :: DL.Session
                                                , ctlConstraints    :: [(Relation, [DL.Relation])]
                                                , ctlDB             :: PG.Connection
                                                , ctlXaction        :: Bool
                                                , ctlXactionLock    :: L.Lock
                                                , ctlBackendRunning :: Bool
                                                , ctlSyncSem        :: MV.MVar Msg
                                                , ctlTermSem        :: MV.MVar ()
                                                , ctlSyncThread     :: T.ThreadId
                                                }

type DaemonState p = (Maybe Handle, ControllerState p)

data Violation = Violation Relation Constraint DL.Fact

instance Show Violation where
    show (Violation rel c f) = "row " ++ show f ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerStart :: FilePath -> Backend p -> String -> FilePath -> FilePath -> Int -> Refine -> p -> IO ()
controllerStart workdir backend dbname dfpath logfile port r switches = do
    let dopts = DaemonOptions{ daemonPort           = port
                             , daemonPidFile        = InHome
                             , printOnDaemonStarted = True}
    lock <- L.new
    xlock <- L.new
    ref <- newIORef (Nothing, ControllerDisconnected workdir backend dbname dfpath r switches xlock False)
    ensureDaemonWithHandlerRunning "cocoon" dopts (controllerLoop lock ref logfile)

controllerLoop :: L.Lock -> IORef (DaemonState p) -> FilePath -> Producer BS.ByteString IO () -> Consumer BS.ByteString IO () -> IO ()
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
        when (not $ ctlBackendRunning state) $
             backendStart (ctlBackend state) (ctlRefine state) (ctlIR state) (cb ref)
        writeIORef ref (Just hlog, state{ctlBackendRunning = True})
        -- serializer and deserializer pipes below are necessary to avoid stalling the pipeline
        -- due to lazy reading
        runEffect (cons <-< serializer <-< commandHandler ref <-< deserializer <-< prod)

-- start transaction
cb :: IORef (DaemonState p) -> PktCB
cb ref f as pkt = do
    lock <- (ctlXactionLock . snd) <$> readIORef ref
    L.acquire lock
    -- read again, as it may have changed between after the previous and before
    -- we acquired the lock
    (_, s) <- readIORef ref
    case s of
         ControllerConnected{..} -> do
             __start s
             (do (Right pkts, _, _, _) <- evalExpr ctlRefine CtxRefine M.empty (Just pkt) ctlDL (eApply f as)
                 _ <- _commit s
                 return pkts
              `catch` (\e -> do _rollback s
                                throw (e::SomeException))) 
         _ -> do L.release lock
                 return []


commandHandler :: IORef (DaemonState p) -> Pipe BS.ByteString BS.ByteString IO ()
commandHandler ref = do
    cmdline <- await
    response <- lift $ (do
        cmd <- case parse cmdGrammar "" (BS.unpack cmdline) of
                    Left  e -> error $ show e
                    Right c -> return c
        case cmd of
             Left c  -> execCommand c ref
             Right e -> execExpr e ref)
         `catch` (\e -> return $ show (e::SomeException))
    yield $ BS.pack response

type Action p = ControllerState p -> IO (ControllerState p, String)

execCommand :: [String] -> IORef (DaemonState p) -> IO String
execCommand cmd ref = case cmd of
                           ["connect"]      -> connect ref
                           ["disconnect"]   -> disconnect ref
                           _                -> do (mh, state) <- readIORef ref
                                                  (state', resp) <- _execCommand cmd state
                                                  writeIORef ref (mh, state')
                                                  return resp
                                                    
_execCommand :: [String] -> Action p
_execCommand ("connect":_)        _       = error "connect does not take arguments" 
_execCommand ("disconnect":_)     _       = error "disconnect does not take arguments"
_execCommand ["start"]            s       = start s
_execCommand ("start":_)          _       = error "start does not take arguments"
_execCommand ["rollback"]         s       = rollback s
_execCommand ("rollback":_)       _       = error "rollback does not take arguments"
_execCommand ["commit"]           s       = commit s
_execCommand ("commit":_)         _       = error "commit does not take arguments"
_execCommand _ ControllerDisconnected{}   = error "command not available in disconnected state"
_execCommand ("show":as)          s       = showcmd as s
_execCommand _                    _       = error "invalid command"

execExpr :: Expr -> IORef (DaemonState p) -> IO String
execExpr e ref = do 
    (_, s) <- readIORef ref
    case s of 
        ControllerConnected{..} ->
            case exprValidate ctlRefine CtxCLI e of
                 Left er -> error er
                 Right _ -> if ctlXaction
                               then do (Left val, vals, _, _) <- evalExpr ctlRefine CtxRefine M.empty Nothing ctlDL e
                                       return $ intercalate ",\n" $ map show $ vals ++ [val]
                               else do _start s
                                       (Left val, vals, _, _) <- evalExpr ctlRefine CtxRefine M.empty Nothing ctlDL e
                                       (do _ <- _commitNotify s
                                           return ()
                                        `catch` \ex -> do 
                                            _rollback s
                                            throw (ex::SomeException))
                                       return $ intercalate ",\n" $ map show $ vals ++ [val]
        _ -> error "execExpr called in disconnected state"
                    

showcmd :: [String] -> Action p
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
    (views, tables) = partition relIsView rels
showcmd _ _ = error $ "Controller.showcmd called in disconnected state"

connect :: IORef (DaemonState p) -> IO String
connect ref = do
    (mh, s) <- readIORef ref
    L.with (ctlXactionLock s) $ do
        case s of 
            ControllerDisconnected{..} -> do
                let ?r = ctlRefine
                db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ ctlDBName
                (do --runEffect $ lift (return $ BS.pack "Connected to database") >~ cons
                    (dl, constr) <- startDLSession ctlDFPath
                    (do xsem  <- MV.newEmptyMVar
                        tsem  <- MV.newEmptyMVar
                        let ?s = ControllerConnected ctlWorkDir ctlBackend ctlDBName ctlDFPath ctlRefine ctlIR dl constr db False ctlXactionLock ctlBackendRunning xsem tsem (error "Controller: unexpected access to ctlSyncThread")
                        populateDB
                        (do syncThr <- T.forkIO $ syncThread ?s
                            let s' = ?s{ctlSyncThread = syncThr}
                            writeIORef ref (mh, s')
                            return "Connected"
                         `catch` \e -> do backendStop ctlBackend
                                          throw (e::SomeException))
                     `catch` \e -> do
                         closeDLSession dl
                         throw (e::SomeException))
                 `catch` \e -> do 
                     PG.close db
                     throw (e::SomeException))
            _ -> throw $ AssertionFailed "already connected"

-- This is the only way to transition to disconnected state.
-- Performs correct cleanup
disconnect :: IORef (DaemonState p) -> IO String
disconnect ref = do
    (mh, s) <- readIORef ref
    case s of 
        ControllerConnected{..} -> do
            (when ctlXaction $ _rollback s) `catch` \e -> error $ "Rollback failed: " ++ show (e :: SomeException)
            L.with ctlXactionLock $ do
                --- send termination notification to sync thread; wait for it to terminate
                _ <- MV.tryTakeMVar ctlSyncSem
                MV.putMVar ctlSyncSem MsgTerminate
                _ <- MV.takeMVar ctlTermSem
                (closeDLSession ctlDL) `catch` \e -> error $ "failed to close Datalog session: " ++ show (e :: SomeException)
                PG.close ctlDB `catch` \e -> error $ "DB disconnect error: " ++ show (e::SomeException)
                writeIORef ref (mh, ControllerDisconnected ctlWorkDir ctlBackend ctlDBName ctlDFPath ctlRefine ctlIR ctlXactionLock ctlBackendRunning)
                return "Disconnected"
        _ -> throw $ AssertionFailed "no active connection"

start :: Action p
start s@ControllerConnected{..} | not ctlXaction = do
    _start s
    return $ (s{ctlXaction = True}, "ok")
                                | otherwise = error "Transaction already in progress"
start ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

rollback :: Action p
rollback s@ControllerConnected{..} | ctlXaction = do
    _rollback s
    return $ (s{ctlXaction = False}, "ok")
                                   | otherwise = error "No transaction in progress"
rollback ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

commit :: Action p
commit s@ControllerConnected{..} | ctlXaction = do
    _ <- _commitNotify s
    return (s{ctlXaction = False}, "ok")
                                 | otherwise = error "No transaction in progress"
commit ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

_start :: ControllerState p -> IO ()
_start s = do 
    let ControllerConnected{..} = s
    L.acquire ctlXactionLock
    DL.start ctlDL

-- assumes we already hold transaction lock
__start :: ControllerState p -> IO ()
__start s = do 
    let ControllerConnected{..} = s
    DL.start ctlDL

_commit :: ControllerState p -> IO ([DL.Fact], [DL.Fact])
_commit s = do
    let ControllerConnected{..} = s
    let ?s = s
    let ?r = ctlRefine
    validateConstraints
    delta <- DL.commit ctlDL
    let (inserts', deletes') = partition snd delta
    let inserts = map fst inserts'
    let deletes = map fst deletes'
    mapM_ (\DL.Fact{..} -> SQL.deleteFrom ctlDB factRel $ map SMT.exprFromSMT factArgs) deletes
    mapM_ (\DL.Fact{..} -> SQL.insertInto ctlDB factRel $ map SMT.exprFromSMT factArgs) inserts
    L.release ctlXactionLock
    return (inserts, deletes)

_commitNotify :: ControllerState p -> IO ([DL.Fact], [DL.Fact])
_commitNotify s = do
    (ins, dels) <- _commit s
    when ((not $ null ins) || (not $ null dels)) $ do putStrLn "Waking up sync thread"
                                                      _ <- MV.tryPutMVar (ctlSyncSem s) MsgSync
                                                      return ()
    return (ins, dels)

_rollback :: ControllerState p -> IO ()
_rollback s = do 
    let ControllerConnected{..} = s
    DL.rollback ctlDL
    L.release ctlXactionLock

startDLSession :: (?r::Refine) => FilePath -> IO (DL.Session, [(Relation, [DL.Relation])])
startDLSession dfpath = do
    let (structs, funcs, rels) = DL.refine2DL ?r
    let (allrels, _) = unzip $ concatMap ( (\(mrel,crels) -> mrel:(concat crels)) . snd) rels
    dl <- DL.newSession dfpath structs funcs allrels
    return (dl, map (mapSnd (map (fst . last) . snd)) rels)

closeDLSession :: DL.Session -> IO ()
closeDLSession dl = DL.closeSession dl

populateDB :: (?r::Refine, ?s::ControllerState p) => IO ()
populateDB = do 
    PG.withTransaction (ctlDB ?s) $ readDB
    validateConstraints
    
validateConstraints :: (?s::ControllerState p) => IO ()
validateConstraints = do
    violations <- checkConstraints 
    let e = intercalate "\n" $ map (("Integrity violation: " ++) . show) violations
    unless (null e) $ throw $ AssertionFailed e

checkConstraints :: (?s::ControllerState p) => IO [Violation]
checkConstraints = 
    (liftM concat) 
    $ mapM (\(rel, dlrels) -> do facts <- mapM (DL.enumRelation (ctlDL ?s) . name) dlrels
                                 return $ concatMap (\(fs, constr) -> map (Violation rel constr) fs) 
                                        $ filter (not . null . fst)
                                        $ zip facts (relConstraints rel)) 
    $ ctlConstraints ?s
   
readDB :: (?r::Refine, ?s::ControllerState p) => IO ()
readDB = mapM_ (\rel -> do rows <- SQL.readTable (ctlDB ?s) rel
                           mapM_ (\args -> (DL.addFact $ ctlDL ?s) 
                                           $ DL.Fact (name rel) (map (SMT.expr2SMT CtxRefine) args)) rows) 
         $ filter (not . relIsView) $ refineRels ?r

syncThread :: ControllerState p -> IO ()
syncThread s = do
    let ControllerConnected{..} = s
    let ?s = s
    sync
    msg <- MV.takeMVar ctlSyncSem
    case msg of
         MsgSync      -> syncThread s
         MsgTerminate -> do sync
                            MV.putMVar ctlTermSem ()
    
sync :: (?s::ControllerState p) => IO ()
sync = do
    putStrLn "Synchronizing"
    let ControllerConnected{..} = ?s
    _start ?s
    (delta, dlfacts) <- readDelta
    -- enabled switch removed from desired or marked as disabled:
    --  * reset switch to clean state if reachable
    mapM_ (\sw -> do let deleted = filter (\(pol,f) -> not pol && (not $ DL.factSwitchFailed ctlRefine f)) $ dlfacts M.! switchRel sw
                     mapM_ (\(_,f) -> ((backendResetSwitch ctlBackend) ctlWorkDir ctlRefine sw f `catch` (\(SomeException _) -> return ()))) deleted)
          $ refineSwitches ctlRefine
    -- relations for which switches have been enabled or created
    let newSwitches = filter (not . null . (dlfacts M.!) . switchRel)
                      $ refineSwitches ctlRefine
    -- read realized tables needed to initialize new switches
    let realized = nub
                   $ concatMap (\sw -> if null $ filter fst $ dlfacts M.! switchRel sw
                                          then []
                                          else let ports = switchPorts ctlRefine $ name sw in
                                               concatMap (portUsesRels ctlRefine . getPort ctlRefine) ports)
                   newSwitches
    reldb <- readRealized realized
    _ <- _commit ?s

    -- new or newly enabled switch in desired:
    --  * reset switch
    --  * buildSwitch from precompiled spec and configure with the current realized state.
    --  * (switch's table 0 is empty at this point, as new ports are not in realized state yet)
    --  * send commands to the switch via ovs-ofctl (starting with resetting to clean state)
    failed <- liftM (map fst . filter (not . snd) . concat)
              $ mapM (\sw -> mapM (\f -> let swid = DL.factSwitchId ctlRefine (switchRel sw) f in
                                         (do (backendBuildSwitch ctlBackend) ctlWorkDir ctlRefine sw f ctlIR reldb
                                             return ((name sw, swid), True))
                                         `catch` (\(SomeException e) -> do putStrLn $ "Failed to initialize switch " ++ name sw ++ "(switch id:" ++ show swid ++ "): " ++ show e
                                                                           return ((name sw, swid), False)))
                             $ filter (not . DL.factSwitchFailed ctlRefine)
                             $ map snd $ filter fst
                             $ dlfacts M.! (switchRel sw))
                     newSwitches
    -- updateSwitch on all enabled switches using the delta DB
    --  * (new switches' table 0 is now populated)
    --  * If any of the updates fail, remember the failed switch
    failed' <- liftM ((failed ++) . map fst . filter (not . snd) . concat)
               $ mapM (\sw -> do swfacts <- liftM (map (\f -> (DL.factSwitchId ctlRefine (switchRel sw) f, f))) $ DL.enumRelation ctlDL (switchRel sw) 
                                 let swfacts' = filter (\(swid, _) -> isNothing $ find (==(name sw, swid)) failed) swfacts
                                 mapM (\(swid, f) -> do (backendUpdateSwitch ctlBackend) ctlWorkDir ctlRefine sw f ctlIR delta
                                                        return ((name sw, swid), True)
                                                     `catch` (\(SomeException e) -> do putStrLn $ "Failed to update switch " ++ name sw ++ " (switch id:" ++ show swid ++ "): " ++ show e
                                                                                       return ((name sw,swid), False)))
                                      swfacts')
               $ refineSwitches ctlRefine
    -- Reconfiguration finished; update the DB (in one transaction):
    --  * add Delta to realized
    --  * mark failed switches in desired (note: only
    --  switches that are still in the desired configuration will be
    --  marked; some of the failed switches may have been deleted by the user)
    _start ?s
    mapM_ (\(pol, DL.Fact rel args) -> let rel' = relRealizedName rel
                                           f = DL.Fact rel' args in
                                       if pol then DL.addFact ctlDL f else DL.removeFact ctlDL f) 
          $ concat $ M.elems dlfacts
    mapM_ (\sw -> do switches <- DL.enumRelation ctlDL (switchRel sw)
                     mapM (\f -> let swid = DL.factSwitchId ctlRefine (switchRel sw) f
                                     f' = DL.factSetSwitchFailed ctlRefine (switchRel sw) f True in
                                 when (elem (name sw, swid) failed') $ do {DL.removeFact ctlDL f; DL.addFact ctlDL f'}) switches)
          $ refineSwitches ctlRefine
    _ <- _commit ?s
    if not $ null failed'
       then do putStrLn $ "failed': " ++ show failed'
               sync
       else return ()

-- read Delta; convert relations used in roles to IR (returns normal relation names)
readDelta :: (?s::ControllerState p) => IO (IR.Delta, M.Map String [(Bool, DL.Fact)])
readDelta = do
   let ControllerConnected{..} = ?s
   let used = refineRelsUsedInPorts ctlRefine
       usedandsw = nub $ used ++ (map switchRel $ refineSwitches ctlRefine)
   ofdelta <- (liftM M.fromList) $ mapM (\rname -> do facts <- DL.enumRelation ctlDL $ relDeltaName rname
                                                      let facts' = map (\(DL.Fact _ ((SMT.EBool p):as)) -> (p, DL.Fact rname as)) facts
                                                      return (rname, facts')) usedandsw
   let irdelta = M.mapWithKey (\rname facts -> 
                                map (mapSnd $ (IR.val2Record ctlRefine (backendStructs ctlBackend) rname) . eStruct rname . map SMT.exprFromSMT . DL.factArgs) facts) 
                 $ M.restrictKeys ofdelta $ S.fromList used
   putStrLn $ "Delta:\n  " ++ 
              (intercalate "\n  " $ map (\(rel, fs) -> rel ++ ":" ++ 
                                                       (intercalate ("\n    ") $ map show fs)) $ M.toList ofdelta)
   return (irdelta, ofdelta)

-- read specified realized relations; convert to IR
readRealized :: (?s::ControllerState p) => [String] -> IO IR.DB
readRealized rels =
    liftM M.fromList
    $ mapM (\rel -> do recs <- enumRelationIR (relRealizedName $ name rel) (name rel)
                       return (name rel, recs))
           rels


enumRelationIR :: (?s::ControllerState p) => String -> String -> IO [IR.Record]
enumRelationIR nrel nconstr = do
    let ControllerConnected{..} = ?s
    facts <- DL.enumRelation ctlDL nrel
    return $ map (IR.val2Record ctlRefine (backendStructs ctlBackend) nconstr . eStruct nconstr . map SMT.exprFromSMT . DL.factArgs) facts
