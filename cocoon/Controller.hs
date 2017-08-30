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
import qualified Control.Concurrent.Lock as L
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
import Role
import NS
import qualified SQL
import qualified Datalog.Datalog         as DL
import qualified Datalog.DataflogSession as DL
import qualified Datalog                 as DL
import qualified SMT                     as SMT
import qualified SMT.SMTSolver           as SMT
import qualified OpenFlow.OpenFlow       as OF
import qualified OpenFlow.OVS            as OF
import qualified OpenFlow.IR2OF          as OF
import qualified IR.IR                   as IR
import qualified IR.Compile2IR           as IR


data ControllerState = ControllerDisconnected { ctlDBName       :: String
                                              , ctlDFPath       :: FilePath
                                              , ctlRefine       :: Refine
                                              , ctlIR           :: OF.IRSwitches
                                              }
                     | ControllerConnected    { ctlDBName       :: String
                                              , ctlDFPath       :: FilePath
                                              , ctlRefine       :: Refine
                                              , ctlIR           :: OF.IRSwitches
                                              , ctlDL           :: DL.Session
                                              , ctlConstraints  :: [(Relation, [DL.Relation])]
                                              , ctlDB           :: PG.Connection
                                              , ctlXaction      :: Bool
                                              }

type DaemonState = (Maybe Handle, ControllerState)

data Violation = Violation Relation Constraint DL.Fact

instance Show Violation where
    show (Violation rel c f) = "row " ++ show f ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerStart :: String -> FilePath -> FilePath -> Int -> Refine -> OF.IRSwitches -> IO ()
controllerStart dbname dfpath logfile port r switches = do
    let dopts = DaemonOptions{ daemonPort           = port
                             , daemonPidFile        = InHome
                             , printOnDaemonStarted = True}
    lock <- L.new
    ref <- newIORef (Nothing, ControllerDisconnected dbname dfpath r switches)
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
         Right _ -> if ctlXaction
                       then do (val ,_) <- evalExpr ctlRefine CtxRefine M.empty ctlDL e
                               return (s, intercalate ",\n" $ map show val)
                       else do DL.start ctlDL
                               (val ,_) <- evalExpr ctlRefine CtxRefine M.empty ctlDL e
                               (do _ <- _commit s
                                   return ()
                                `catch` \ex -> do 
                                    DL.rollback ctlDL
                                    throw (ex::SomeException))
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
    (views, tables) = partition relIsView rels
showcmd _ _ = error $ "Controller.showcmd called in disconnected state"

connect :: Action
connect ControllerDisconnected{..} = do
    let ?r = ctlRefine
    db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ ctlDBName
    (do --runEffect $ lift (return $ BS.pack "Connected to database") >~ cons
        (dl, constr) <- startDLSession ctlDFPath
        (do let ?s = ControllerConnected ctlDBName ctlDFPath ctlRefine ctlIR dl constr db False
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
    return $ (ControllerDisconnected ctlDBName ctlDFPath ctlRefine ctlIR, "Disconnected")
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
    _ <- _commit s
    return (s{ctlXaction = False}, "ok")
                                 | otherwise = error "No transaction in progress"
commit ControllerDisconnected{} = throw $ AssertionFailed "no active connection"

_commit :: ControllerState -> IO ([DL.Fact], [DL.Fact])
_commit s = do
    let ?s = s
    let ?r = ctlRefine s
    validateConstraints
    delta <- DL.commit $ ctlDL s
    let (inserts', deletes') = partition snd delta
    let inserts = map fst inserts'
    let deletes = map fst deletes'
    mapM_ (\DL.Fact{..} -> SQL.deleteFrom (ctlDB s) factRel $ map SMT.exprFromSMT factArgs) deletes
    mapM_ (\DL.Fact{..} -> SQL.insertInto (ctlDB s) factRel $ map SMT.exprFromSMT factArgs) inserts
    return (inserts, deletes)

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
    let e = intercalate "\n" $ map (("Integrity violation: " ++) . show) violations
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


factField :: (?s::ControllerState) => DL.Fact -> (Expr -> Expr) -> Expr
factField (DL.Fact rel as) g = evalConstExpr (ctlRefine ?s) $ g (eStruct rel $ map SMT.exprFromSMT as)

sync :: (?s::ControllerState) => IO ()
sync = do
    let ControllerConnected{..} = ?s
        factSwitchId rel f = let Just [key] = relPrimaryKey rel
                                 e = mkkey key
                                 mkkey (E (EVar _ v))     e' = eField e' v
                                 mkkey (E (EField _ x a)) e' = eField (mkkey x e') a
                                 mkkey x                  _  = error $ "Controller.sync: mmkkey " ++ show x
                                 E (EBit _ _ swid) = factField f (mkkey key)
                             in swid
        factSwitchFailed rel f = let E (EBool _ fl) = factField f (\v -> eField v "failed") in fl
        factSetSwitchFailed rel (DL.Fact n as) fl = let Just i = findIndex ((=="failed") . name) $ relArgs rel
                                                    in DL.Fact n $ take i as ++ (SMT.EBool fl : drop (i+1) as)

    (delta, dlfacts) <- readDelta
    -- enabled switch removed from desired or marked as disabled:
    --  * reset switch to clean state if reachable
    mapM_ (\rel -> do let deleted = filter (\(pol,f) -> not pol && (not $ factSwitchFailed rel f)) $ dlfacts M.! name rel
                      mapM_ (\(_,f) -> (resetSwitch f) `catch` (\(SomeException _) -> return ())) deleted)
          $ refineSwitchRels ctlRefine
    -- relations for which switches have been enabled or created
    let newSwRels = filter (not . null . (delta M.!) . name)
                    $ refineSwitchRels ctlRefine
    -- read realized tables needed to initialize new switches
    let realized = nub
                   $ concatMap (\rel -> if null $ filter fst $ delta M.! name rel
                                           then []
                                           else let ports = relSwitchPorts ctlRefine rel in
                                                concatMap (roleUsesRels ctlRefine . getRole ctlRefine . fst . annotRoles . fromJust . relAnnotation) ports)
                   newSwRels
    reldb <- readRealized realized
    -- new or newly enabled switch in desired:
    --  * reset switch
    --  * buildSwitch from precompiled spec and configure with the current realized state.
    --  * (switch's table 0 is empty at this point, as new ports are not in realized state yet)
    --  * send commands to the switch via ovs-ofctl (starting with resetting to clean state)
    failed <- liftM (map fst . filter (not . snd) . concat)
              $ mapM (\rel -> mapM (\f -> let swid = factSwitchId rel f
                                              cmds = OF.buildSwitch ctlRefine (ctlIR M.! name rel) reldb swid in
                                              do resetSwitch f
                                                 sendCmds f cmds
                                                 return ((name rel, swid), True)
                                              `catch` (\(SomeException _) -> return ((name rel, swid), False)))
                              $ filter (not . factSwitchFailed rel)
                              $ map snd $ filter fst
                              $ dlfacts M.! (name rel))
                     newSwRels
    -- updateSwitch on all enabled switches using the delta DB
    --  * (new switches' table 0 is now populated)
    --  * If any of the updates fail, remember the failed switch
    failed' <- liftM ((failed ++) . map fst . filter (not . snd) . concat)
               $ mapM (\rel -> do swfacts <- liftM (map (\f -> (factSwitchId rel f, f))) $ DL.enumRelation ctlDL (name rel) 
                                  let swfacts' = filter (\(swid, _) -> isNothing $ find (==(name rel, swid)) failed) swfacts
                                  mapM (\(swid, f) -> do let cmds = OF.updateSwitch ctlRefine (ctlIR M.! name rel) swid delta
                                                         sendCmds f cmds
                                                         return ((name rel, swid), True)
                                                      `catch` (\(SomeException _) -> return ((name rel,swid), False)))
                                        swfacts')
               $ refineSwitchRels ctlRefine
    -- Reconfiguration finished; update the DB (in one transaction):
    --  * add Delta to realized
    --  * mark failed switches as disabled in desired 
    DL.start ctlDL
    mapM_ (\(pol, DL.Fact rel args) -> let rel' = relRealizedName rel
                                           f = DL.Fact rel' args in
                                       if pol then DL.addFact ctlDL f else DL.removeFact ctlDL f) 
          $ concat $ M.elems dlfacts
    mapM_ (\rel -> do switches <- DL.enumRelation ctlDL (name rel)
                      mapM (\f -> let swid = factSwitchId rel f
                                      f' = factSetSwitchFailed rel f False in
                                  when (elem (name rel, swid) failed') $ do {DL.removeFact ctlDL f; DL.addFact ctlDL f'}) switches)
          $ refineSwitchRels ctlRefine
    _ <- DL.commit ctlDL
    return ()

-- send OpenFlow commands to the switch; returns False in case of
-- failure
sendCmds :: (?s::ControllerState) => DL.Fact -> [OF.Command] -> IO ()
sendCmds f cmds = 
    let E (EString _ swaddr) = factField f (\v -> eField v "address")
        E (EString _ swname) = factField f (\v -> eField v "name")
    in OF.ovsSendCmds swaddr swname cmds

resetSwitch :: (?s::ControllerState) => DL.Fact -> IO ()
resetSwitch f = 
    let E (EString _ swaddr) = factField f (\v -> eField v "address")
        E (EString _ swname) = factField f (\v -> eField v "name")
    in OF.ovsReset swaddr swname

-- read Delta; convert relations used in roles to IR (returns normal relation names)
readDelta :: (?s::ControllerState) => IO (IR.Delta, M.Map String [(Bool, DL.Fact)])
readDelta = do
   let ControllerConnected{..} = ?s
   let used = refineRelsUsedInRoles ctlRefine
       usedandsw = nub $ used ++ (map name $ refineSwitchRels ctlRefine)
   ofdelta <- (liftM M.fromList) $ mapM (\rname -> do facts <- DL.enumRelation ctlDL $ relDeltaName rname
                                                      let facts' = map (\(DL.Fact _ ((SMT.EBool p):as)) -> (p, DL.Fact rname as)) facts
                                                      return (rname, facts')) usedandsw
   let irdelta = M.mapWithKey (\rname facts -> 
                                map (mapSnd $ (IR.val2Record ctlRefine rname) . eStruct rname . map SMT.exprFromSMT . DL.factArgs) facts) 
                 $ M.restrictKeys ofdelta $ S.fromList used
   return (irdelta, ofdelta)

-- read specified realized relations; convert to IR
readRealized :: (?s::ControllerState) => [String] -> IO IR.DB
readRealized rels =
    liftM M.fromList
    $ mapM (\rel -> do recs <- enumRelationIR (relRealizedName $ name rel) (name rel)
                       return (name rel, recs))
           rels


enumRelationIR :: (?s::ControllerState) => String -> String -> IO [IR.Record]
enumRelationIR nrel nconstr = do
    facts <- DL.enumRelation (ctlDL ?s) nrel
    return $ map (IR.val2Record (ctlRefine ?s) nconstr . eStruct nconstr . map SMT.exprFromSMT . DL.factArgs) facts

-- :validate
--
--insert relname (<val1>, <val2>)
--the (p in <relation> | <cond>) p
--
--every request is a transaction
