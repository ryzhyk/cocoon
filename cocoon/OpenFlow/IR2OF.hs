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

{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, FlexibleContexts #-}

module OpenFlow.IR2OF( IRSwitch
                     , IRSwitches
                     , precompile
                     , buildSwitch
                     , updateSwitch
                     , recordField) where

import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Query.DFS as G
import qualified Data.Map                       as M
import Data.List
import Data.Maybe
import Data.Bits
import Control.Monad
import Control.Monad.Except
import Debug.Trace
import System.FilePath.Posix
import System.IO.Unsafe

import Util
import Ops
import Name
import qualified IR.IR             as I
import qualified IR.Compile2IR     as I
import qualified IR.Registers      as I
import qualified OpenFlow.OpenFlow as O
import qualified Backend           as B
import qualified Syntax            as C -- Cocoon
import qualified Relation          as C
import qualified NS                as C

-- Uniquely identify an instance of the switch:
-- (SwitchRelation, primary key)
type SwitchId = Integer

type IRSwitch = [(String, I.Pipeline)]
type IRSwitches = M.Map String IRSwitch

maxOFTables = 255

-- For each switch table
--  Compute and compile all port roles, perform register and OF table allocation
precompile :: (MonadError String me) => B.StructReify -> FilePath -> C.Refine -> I.RegisterFile -> me IRSwitches
precompile structs workdir r rfile = do
    let swrels = filter C.relIsSwitch $ C.refineRels r
    (liftM M.fromList) 
     $ mapM (\rel -> do let ir = I.compileSwitch structs workdir r rel
                        ir' <- mapM (\(n, pl) -> do pl' <- I.allocVarsToRegisters pl rfile
                                                    let rdotname = workdir </> addExtension (addExtension n "reg") "dot"
                                                    trace (unsafePerformIO $ do {I.cfgDump (I.plCFG pl') rdotname; return ""}) $ return (n, pl')
                                                 `catchError` (\e -> throwError $ "Compiling port " ++ n ++ " of " ++ name rel ++ ":" ++ e)) ir
                        let (ntables, ir'') = assignTables ir'
                        mapM_ (\(n, pl) -> do let dotname = workdir </> addExtension (addExtension n "of") "dot"
                                              trace (unsafePerformIO $ do {I.cfgDump (I.plCFG pl) dotname; return ""}) $ return ()) ir''
                        when (ntables > maxOFTables) 
                            $ throwError $ name rel ++ " requires " ++ show ntables ++ " OpenFlow tables, but only " ++ show maxOFTables ++ " tables are available"
                        return (name rel, ir'')) swrels

-- Relabel port CFGs into openflow table numbers
assignTables :: IRSwitch -> (Int, IRSwitch)
assignTables pls = foldl' (\(start, pls') (n,pl) -> let (start', pl') = relabel start pl
                                                    in (start', pls' ++ [(n, pl')])) (1, pls) pls
    where 
    relabel :: Int -> I.Pipeline -> (Int, I.Pipeline)
    relabel start pl = (start + length ordered, pl{I.plCFG = cfg', I.plEntryNode = start})
        where
        ordered = G.topsort $ I.plCFG pl
        rename nd = (fromJust $ findIndex (nd==) ordered) + start
        bbrename (I.BB as (I.Goto nd)) = I.BB as $ I.Goto $ rename nd
        bbrename bb                    = bb
        cfg' = G.buildGr
               $ G.ufold (\(pre, nd, node, suc) cs -> let pre'  = map (mapSnd rename) pre
                                                          suc'  = map (mapSnd rename) suc
                                                          nd'   = rename nd 
                                                          node' = I.mapBB bbrename node
                                                      in (pre', nd', node', suc'):cs) 
                 [] (I.plCFG pl)

-- New switch event
--   Store the list of tables this switch depends on
buildSwitch :: C.Refine -> IRSwitch -> I.DB -> SwitchId -> [O.Command]
buildSwitch r ports db swid = table0 : (staticcmds ++ updcmds)
    where
    table0 = O.AddFlow 0 $ O.Flow 0 [] [O.ActionDrop]
    -- Configure static part of the pipeline
    staticcmds = concatMap (\(_, pl) -> concatMap (mkNode pl) $ G.labNodes $ I.plCFG pl) ports
    -- Configure dynamic part from primary tables
    updcmds = updateSwitch r ports swid (M.map (map (True,)) db)

updateSwitch :: C.Refine -> IRSwitch -> SwitchId -> I.Delta -> [O.Command]
updateSwitch r ports swid db = portcmds ++ nodecmds
    where
    -- update table0 if ports have been added or removed
    portcmds = concatMap (\(prole, pl) -> updatePort r (prole,pl) swid db) ports
    -- update pipeline nodes
    nodecmds = concatMap (\(_, pl) -> concatMap (updateNode r db pl) $ G.labNodes $ I.plCFG pl) ports

updatePort :: C.Refine -> (String, I.Pipeline) -> SwitchId -> I.Delta -> [O.Command]
updatePort r (prole, pl) i db = delcmd ++ addcmd
    where
    prel = name $ C.roleTable $ C.getRole r prole
    (add, del) = partition fst $ filter (\(_, f) -> I.exprIntVal (f M.! "switch") == i) $ db M.! prel
    match f = let pnum = f M.! "portnum" in
             mkSimpleCond M.empty $ I.EBinOp Eq (I.EPktField "portnum" $ I.TBit $ I.exprWidth pnum) pnum
    delcmd = concatMap (\(_,f) -> map (O.DelFlow 0 1) $ match f) del
    addcmd = concatMap (\(_,f) -> map (\m -> O.AddFlow 0 $ O.Flow 1 m [mkGoto pl $ I.plEntryNode pl]) $ match f) add

mkNode :: I.Pipeline -> (I.NodeId, I.Node) -> [O.Command]
mkNode pl (nd, node) = 
    case node of
         I.Par bs            -> [ O.AddGroup $ O.Group nd O.GroupAll $ map (O.Bucket Nothing . mkStaticBB pl) bs 
                                , O.AddFlow nd $ O.Flow 0 [] [O.ActionGroup nd] ]
         I.Cond cs           -> map (\(m, a) -> O.AddFlow nd $ O.Flow 0 m a) $ mkCond $ map (mapSnd (mkStaticBB pl)) cs
         I.Lookup _ _ _ _ el -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB pl el]
         I.Fork{}            -> [O.AddGroup $ O.Group nd O.GroupAll []]

updateNode :: C.Refine -> I.Delta -> I.Pipeline -> (I.NodeId, I.Node) -> [O.Command]
updateNode r db portpl (nd, node) = 
    case node of
         I.Par _              -> []
         I.Cond _             -> []
         I.Lookup t _ pl th _ -> let (add, del) = partition fst (db M.! t) 
                                     delcmd = concatMap (\(_,f) -> map (\O.Flow{..} -> O.DelFlow nd flowPriority flowMatch) 
                                                                       $ mkLookupFlow portpl f pl th) del
                                     addcmd = concatMap (\(_,f) -> map (O.AddFlow nd) $ mkLookupFlow portpl f pl th) add
                                 in delcmd ++ addcmd
         I.Fork t _ _ b       -> -- create a bucket for each table row
                                 let (add, del) = partition fst (db M.! t) 
                                     delcmd = map (\(_,f) -> O.DelBucket nd $ getBucketId r t f) del
                                     addcmd = map (\(_,f) -> O.AddBucket nd $ O.Bucket (Just $ getBucketId r t f) $ mkBB portpl f b) add
                                 in delcmd ++ addcmd

getBucketId :: C.Refine -> String -> I.Record -> O.BucketId
getBucketId r rname f = fromInteger pkey
    where   
    rel = C.getRelation r rname
    Just [key] = C.relPrimaryKey rel
    I.EBit _ pkey = recordField f key

recordField :: I.Record -> C.Expr -> I.Expr
recordField rec fexpr = rec M.! fname
    where
    fname = mkname fexpr
    mkname (C.E (C.EVar _ v))      = v
    mkname (C.E (C.EField _ e fl)) = mkname e I..+ fl
    mkname e                       = error $ "IR2OF.mkname " ++ show e

mkStaticBB :: I.Pipeline -> I.BB -> [O.Action]
mkStaticBB pl b = mkBB pl (error "IR2OF.mkStaticBB requesting field value") b

mkBB :: I.Pipeline -> I.Record -> I.BB -> [O.Action]
mkBB pl val (I.BB as n) = map (mkAction val) as ++ [mkNext pl val n]

mkAction :: I.Record -> I.Action -> O.Action
mkAction val (I.ASet e1 e2) = O.ActionSet (mkExpr val e1) (mkExpr val e2)
mkAction _   a              = error $ "not implemented: IR2OF.mkAction" ++ show a

mkExpr :: I.Record -> I.Expr -> O.Expr
mkExpr val e = 
    case e of
         I.EPktField f t   -> O.EField (O.Field f $ I.typeWidth t) Nothing
         I.EVar      v t   -> O.EField (O.Field v $ I.typeWidth t) Nothing
         I.ECol      c _   -> case M.lookup c val of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown column: " ++ show c
                                   Just v  -> mkExpr val v
         I.ESlice    x h l -> slice (mkExpr val x) h l
         I.EBit      w v   -> O.EVal $ O.Value w v
         _                 -> error $ "Not implemented: IR2OF.mkExpr " ++ show e

slice :: O.Expr -> Int -> Int -> O.Expr
slice (O.EField f Nothing)       h l = O.EField f $ Just (h, l)
slice (O.EField f (Just (_,l0))) h l = O.EField f $ Just (l0+h, l0+l)
slice (O.EVal (O.Value _ v))     h l = O.EVal $ O.Value (h-l) $ bitSlice v h l

mkLookupFlow :: I.Pipeline -> I.Record -> I.Pipeline -> I.BB -> [O.Flow]
mkLookupFlow pl val lpl b = map (\m -> O.Flow 1 m as) matches
    where
    matches = mkPLMatch lpl val
    as = mkBB pl val b
    
mkCond :: [(I.Expr, [O.Action])] -> [([O.Match], [O.Action])]
mkCond []          = [([], [O.ActionDrop])]
mkCond ((c, a):cs) = mkCond' c [([], a)] $ mkCond cs

mkCond' :: I.Expr -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])]
mkCond' c yes no = 
    case c of
         I.EBinOp Eq e1 e2 | isbool e1 -> mkCond' e1 (mkCond' e2 yes no) (mkCond' e2 no yes)
                           | otherwise -> let cs' = mkMatch (mkExpr M.empty e1) (mkExpr M.empty e2)
                                          in concatMap (\c' -> mapMaybe (\(m,a) -> fmap (,a) (concatMatches c' m)) yes) cs' ++ no
         I.EBinOp Neq e1 e2            -> mkCond' (I.EUnOp Not (I.EBinOp Eq e1 e2)) yes no
         I.EBinOp Impl e1 e2           -> mkCond' (I.EBinOp Or (I.EUnOp Not e1) e2) yes no
         I.EUnOp Not e                 -> mkCond' e no yes
         I.EBinOp Or e1 e2             -> mkCond' e1 yes (mkCond' e2 yes no)
         I.EBinOp And e1 e2            -> mkCond' e1 (mkCond' e2 yes no) no
         _                             -> error $ "IR2OF.mkCond': expression is not supported: " ++ show c

isbool :: I.Expr -> Bool
isbool I.EBool{}               = True
isbool (I.ECol _ I.TBool)      = True
isbool (I.EPktField _ I.TBool) = True
isbool (I.EBinOp op _ _)       = bopReturnsBool op
isbool (I.EUnOp Not _)         = True
isbool _                       = False

-- TODO: use BDDs to encode arbitrary pipelines
mkPLMatch :: I.Pipeline -> I.Record -> [[O.Match]]
mkPLMatch I.Pipeline{..} val = 
    if G.size plCFG == 2 
       then case G.lab plCFG plEntryNode of
                 Just (I.Cond cs) -> mkSimpleCond val $ cs2expr cs
                 _                -> error "IR2OF.mkPLMatch: CFG too complicated"
       else error "IR2OF.mkPLMatch: CFG too complicated (<> 2 nodes)"
    -- IR compiler encodes lookup conditions with satisfying branches terminating in Drop
    where
    cs2expr ((c, I.BB [] I.Drop):cs) = I.EBinOp Or c $ cs2expr cs
    cs2expr ((c, _):cs)              = I.EBinOp And (I.EUnOp Not c) $ cs2expr cs
    cs2expr []                       = I.EBool False 

mkSimpleCond :: I.Record -> I.Expr -> [[O.Match]]
mkSimpleCond val c = 
    case c of
         I.EBinOp Eq e1 e2 | not (isbool e1) 
                                     -> mkMatch (mkExpr val e1) (mkExpr val e2)
         I.EBinOp Neq e1 e2          -> mkSimpleCond val (I.EUnOp Not (I.EBinOp Eq e1 e2))
         I.EBinOp Impl e1 e2         -> mkSimpleCond val (I.EBinOp Or (I.EUnOp Not e1) e2)
         I.EBinOp Or e1 e2           -> mkSimpleCond val e1 ++ mkSimpleCond val e2
         I.EBinOp And e1 e2          -> catMaybes $ concatMatches <$> mkSimpleCond val e1 <*> mkSimpleCond val e2
         I.EUnOp Not (I.EBool b)     -> mkSimpleCond val $ I.EBool (not b)
         I.EUnOp Not (I.EUnOp Not e) -> mkSimpleCond val e
         I.EBool False               -> []
         I.EBool True                -> [[]]
         _                           -> error $ "IR2OF.mkPLMatch': expression is not supported: " ++ show c

concatMatches :: [O.Match] -> [O.Match] -> Maybe [O.Match]
concatMatches m1 m2 = foldM (\ms m@(O.Match f msk v) -> 
                              case findIndex ((== f) . O.matchField) ms of
                                   Just i  -> do let O.Match _ msk' v' = ms !! i
                                                 m' <- combineMatches f (msk', v') (msk, v)
                                                 return $ (take i ms) ++ [m'] ++ (drop (i+1) ms)
                                   Nothing -> return $ ms ++ [m]) m1 m2 

combineMatches :: O.Field -> (Maybe O.Mask, O.Value) -> (Maybe O.Mask, O.Value) -> Maybe O.Match
combineMatches f (mm1, O.Value w v1) (mm2, O.Value _ v2) = if v1' == v2' then Just (O.Match f m' $ O.Value w v') else Nothing
    where m1 = case mm1 of
                    Nothing            -> -1
                    Just (O.Value _ m) -> m
          m2 = case mm2 of
                    Nothing            -> -1
                    Just (O.Value _ m) -> m
          v1' = v1 .&. m1 .&. m2
          v2' = v2 .&. m1 .&. m2
          m' = if m1 .|. m2 == -1 then Nothing else Just (O.Value w $ m1 .|. m2)
          v' = (v1 .&. m1) .|. (v2 .&. m2)

mkMatch :: O.Expr -> O.Expr -> [[O.Match]]
mkMatch e1 e2 | const1 && const2 && v1 == v2 = [[]]
              | const1 && const2 && v1 /= v2 = []
              | const1                       = mkMatch e2 e1
              | const2                       = [[O.Match f (slice2mask f sl) v2]]
              | otherwise                    = error $ "IR2OF.mkMatch: cannot match two variables: " ++ show e1 ++ " " ++ show e2
    where
    const1 = O.exprIsConst e1
    const2 = O.exprIsConst e2
    (O.EVal v1) = e1
    (O.EVal v2) = e2
    (O.EField f sl) = e1
    slice2mask :: O.Field -> Maybe (Int, Int) -> Maybe O.Mask
    slice2mask fl msl = fmap (O.Value (O.fieldWidth fl) . uncurry bitRange) msl

mkNext :: I.Pipeline -> I.Record -> I.Next -> O.Action
mkNext pl _ (I.Goto nd) = mkGoto pl nd
mkNext _  r (I.Send e)  = O.ActionOutput $ mkExpr r e
mkNext _  _ I.Drop      = O.ActionDrop

mkGoto :: I.Pipeline -> I.NodeId -> O.Action
mkGoto pl nd = 
    case G.lab (I.plCFG pl) nd of
         Just (I.Fork{}) -> O.ActionGroup nd
         _               -> O.ActionGoto nd 
