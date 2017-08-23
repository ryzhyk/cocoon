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

{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

module OpenFlow.IR2OF( buildSwitch
                     , updateSwitch) where

import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Query.DFS as G
import qualified Data.Map                       as M
import Data.List
import Data.Maybe

import Util
import Ops
import Name
import qualified IR.IR             as I
import qualified IR.Compile2IR     as I
import qualified OpenFlow.OpenFlow as O
import qualified Syntax            as C -- Cocoon
import qualified Relation          as C
import qualified NS                as C

type IRSwitch = [(String, I.Pipeline)]
type IRSwitches = M.Map String IRSwitch

-- Uniquely identify an instance of the switch:
-- (SwitchRelation, primary key)
type SwitchId = (String, Integer)

fieldMap :: M.Map I.FieldName O.Field
fieldMap = undefined

-- For each switch table
--  Compute and compile all port roles
precompile :: C.Refine -> IRSwitches
precompile r = M.fromList 
               $ map (\rel -> (name rel, assignTables $ I.compileSwitch r rel)) 
               $ filter C.relIsSwitch $ C.refineRels r

-- Relabel port CFGs into openflow table numbers
assignTables :: IRSwitch -> IRSwitch
assignTables pls = snd $ foldl' (\(start, pls') (n,pl) -> let (start', pl') = relabel start pl
                                                          in (start', pls' ++ [(n, pl')])) (1, pls) pls
    where 
    relabel :: Int -> I.Pipeline -> (Int, I.Pipeline)
    relabel start pl = (start + length ordered, pl{I.plCFG = cfg', I.plEntryNode = start})
        where
        ordered = G.topsort $ I.plCFG pl
        rename nd = (fromJust $ findIndex (nd==) ordered) + start
        bbrename (I.BB as (I.Goto nd)) = I.BB as $ I.Goto $ rename nd
        bbrename bb                    = bb
        cfg' = G.gmap (\(pre, nd, node, suc) -> let pre'  = map (mapSnd rename) pre
                                                    suc'  = map (mapSnd rename) suc
                                                    nd'   = rename nd 
                                                    node' = I.mapBB bbrename node
                                                in (pre', nd', node', suc')) 
                      $ I.plCFG pl

-- TODO: move to a non-OF-specific file
-- Data structure to represent database delta 
-- or a complete snapshot.  Maps relation name into 
-- a set of facts with polarities.
type Delta = M.Map String [(Bool, I.Record)]
type DB    = M.Map String [I.Record]

-- TODO backend-independent update procedure:
-- read all deltas in one transaction
-- update each switch from deltas
-- update realized state

-- New switch event
--   Store the list of tables this switch depends on
buildSwitch :: IRSwitch -> DB -> SwitchId -> [O.Command]
buildSwitch ports db swid = table0 : (staticcmds ++ updcmds)
    where
    table0 = O.AddFlow 0 $ O.Flow 0 [] [O.ActionDrop]
    -- Configure static part of the pipeline
    staticcmds = concatMap (\(_, pl) -> concatMap mkNode $ G.labNodes $ I.plCFG pl) ports
    -- Configure dynamic part from primary tables
    updcmds = updateSwitch ports swid (M.map (map (True,)) db)

updateSwitch :: IRSwitch -> SwitchId -> Delta -> [O.Command]
updateSwitch ports swid db = portcmds ++ nodecmds
    where
    -- update table0 if ports have been added or removed
    portcmds = concatMap (\(prel, pl) -> updatePort (prel,pl) swid db) ports
    -- update pipeline nodes
    nodecmds = concatMap (\(_, pl) -> concatMap (updateNode db pl) $ G.labNodes $ I.plCFG pl) ports

updatePort :: (String, I.Pipeline) -> SwitchId -> Delta -> [O.Command]
updatePort (prel, pl) (swrel, i) db = delcmd ++ addcmd
    where
    (add, del) = partition fst $ filter (\(pol, f) -> I.exprIntVal (f M.! "switch") == i) $ db M.! prel
    match f = mkSimpleCond $ I.EBinOp Eq (I.EPktField "portnum") (f M.! "portnum")
    delcmd = concatMap (\(_,f) -> map (O.DelFlow 0 1) $ match f) del
    addcmd = concatMap (\(_,f) -> map (\m -> O.AddFlow 0 $ O.Flow 1 m [mkGoto pl $ I.plEntryNode pl]) $ match f) del

mkNode :: (I.NodeId, I.Node) -> [O.Command]
mkNode (nd, node) = 
    case node of
         I.Par bs               -> [ O.AddGroup $ O.Group nd O.GroupAll $ map (O.Bucket Nothing . mkStaticBB) bs 
                                   , O.AddFlow nd $ O.Flow 0 [] [O.ActionGroup nd] ]
         I.Cond cs              -> concatMap (\(c,b) -> map (\(m, a) -> O.AddFlow nd $ O.Flow 0 m a) $ mkCond [(c, mkStaticBB b)]) cs
         I.Lookup t vs pl th el -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB el]
         I.Fork t vs pl b       -> [O.AddGroup $ O.Group nd O.GroupAll []]

updateNode :: Delta -> I.Pipeline -> (I.NodeId, I.Node) -> [O.Command]
updateNode db portpl (nd, node) = 
    case node of
         I.Par bs               -> []
         I.Cond cs              -> []
         I.Lookup t vs pl th el -> let (add, del) = partition fst (db M.! t) 
                                       delcmd = map (\(_,f) -> let O.Flow{..} = mkLookupFlow t portpl f pl th
                                                               in O.DelFlow nd 1 flowPriority flowMatch) del
                                       addcmd = map (\(_,f) -> O.AddFlow nd 1 $ mkLookupFlow t portpl f pl th) add
                                   in delcmd ++ addcmd
         I.Fork t vs _ b        -> -- create a bucket for each table row
                                   let (add, del) = partition fst (db M.! t) 
                                       delcmd = map (\(_,f) -> O.DelBucket nd $ getBucketId t f) del
                                       addcmd = map (\(_,f) -> O.AddBucket nd $ O.Bucket (Just $ getBucketId t f) $ mkBB portpl f b) add
                                   in delcmd ++ addcmd

getBucketId :: (?r::C.Refine) => String -> I.Record -> O.BucketId
getBucketId rname f = f M.! pkeyname
    where   
    rel = getRelation ?r rname
    Just [key] = relPrimaryKey rel
    pkeyname = mkkey key
    mkkey (C.E (C.EVar _ v))     = v
    mkkey (C.E (C.EField _ e f)) = mkkey e I..+ f

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
         I.EPktField f     -> case fieldMap M.! f of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown field: " ++ show f
                                   Just f' -> O.EField f' 
         I.EVar      v     -> case fieldMap M.! v of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown variable: " ++ show v
                                   Just v' -> O.EField v'
         I.ECol      c     -> case val M.! c of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown column: " ++ show c
                                   Just v  -> mkExpr val v
         I.ESlice    x h l -> slice (mkExpr val x) h l
         I.EBit      w v   -> O.EVal $ O.Value w v
         _                 -> error $ "Not implemented: IR2OF.mkExpr " ++ show e


mkLookupFlow :: (?r::C.Refine) => String -> I.Pipeline -> I.Record -> I.Pipeline -> I.BB -> [O.Flow]
mkLookupFlow t pl val lpl b = map (\m -> O.Flow 1 m as) matches
    where
    matches = mkPLMatch lpl val
    as = mkBB pl val b
    
mkCond :: [(I.Expr, [O.Action])] -> [([O.Match], [O.Action])]
mkCond [(c, a)] = mkCond' c [([], a)] [([], [O.ActionDrop])]

mkCond' :: I.Expr -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])] -> [([O.Match], [O.Action])]
mkCond' c yes no = 
    case c of
         I.EBinOp Eq e1 e2 | isBool e1 -> mkCond' e1 (mkCond' e2 yes no) (mkCond' e2 no yes)
                           | otherwise -> let c' = mkMatch (mkExpr e1) (mkExpr e2)
                                          in (map (\(m,a) -> concatMatches c' m, a) yes) ++ no
         I.EBinOp Neq e1 e2            -> mkCond' (I.EUnOp Not (I.EBinOp Eq e1 e2)) yes no
         I.EBinOp Impl e1 e2           -> mkCond' (I.EBinOp Or (I.EUnOp Not e1) e1) yes no
         I.EUnOp Not e                 -> mkCond' e no yes
         I.EBinOp Or e1 e2             -> mkCond' e1 yes (mkCond' e2 yes no)
         I.EBinOp And e1 e2            -> mkCond' e1 (mkCond' e2 yes no) no
         _                             -> error $ "IR2OF.mkCond': expression is not supported: " ++ show e


-- TODO: use BDDs to encode arbitrary pipelines
mkPLMatch :: I.Pipeline -> I.Record -> [[O.Match]]
mkPLMatch I.Pipeline{..} val = 
    if G.size plCFG == 2 
       then case G.lab cfg' plEntryNode of
                 I.Cond cs -> mkPLMatch' $ cs2expr cs
                 _         -> error "IR2OF.mkPLMatch: CFG too complicated"
       else error "IR2OF.mkPLMatch: CFG too complicated (<> 2 nodes)"
    -- IR compiler encodes lookup conditions with satisfying branches terminating in Drop
    where
    cs2expr ((c, I.BB [] I.Drop):cs) = I.EBinOp Or c $ cs2expr cs
    cs2expr ((c, _):cs)              = I.EBinOp And (EUnOp Not c) $ cs2expr cs
    cs2expr []                       = I.EBool False 

mkSimpleCond :: I.Expr -> [[O.Match]]
mkSimpleCond c = 
    case c of
         I.EBinOp Eq e1 e2 | not (isBool e1) -> mkMatch (mkExpr e1) (mkExpr e2)
         I.EBinOp Neq e1 e2                  -> mkPLMatch' (I.EUnOp Not (I.EBinOp Eq e1 e2))
         I.EBinOp Impl e1 e2                 -> mkPLMatch' (I.EBinOp Or (I.EUnOp Not e1) e1)
         I.EBinOp Or e1 e2                   -> mkPLMatch' e1 ++ mkPLMatch' e2
         I.EBinOp And e1 e2                  -> catMaybes $ concatMatches <$> mkPLMatch' e1 <*> mkPLMatch' e2
         I.EUnOp Not (I.EBool b)             -> mkPLMatch' $ I.EBool (not b)
         I.EUnOp Not (Not e)                 -> mkPLMatch' e
         I.EBool False                       -> []
         I.EBool True                        -> [[]]
         _                                   -> error $ "IR2OF.mkPLMatch': expression is not supported: " ++ show e

concatMatches :: [O.Match] -> [O.Match] -> Maybe [O.Match]
concatMatches m1 m2 = foldM (\ms m@(O.Match f msk v) -> 
                              case findIndex ((== f) . matchField) ms of
                                   Just i  -> do let O.Match _ msk' v' = ms !! i
                                                 m' <- combineMatches f (msk', v') (msk, v)
                                                 return $ (take i ms) ++ [m'] ++ (drop (i+1) ms)
                                   Nothing -> return $ ms ++ [m]) m1 m2 

combineMatches :: O.Field -> (Maybe O.Mask, O.Value) -> (Maybe O.Mask, O.Value) -> Maybe O.Match
combineMatches f (mm1, O.Value w v1) (mm2, O.Value _ v2) = if v1' == v2' then Just (O.Match f m' $ O.Value w v') else Nothing
    where m1 = case mm1 of
                    Nothing           -> -1
                    Just (O.Mask _ m) -> m
          m2 = case mm2 of
                    Nothing           -> -1
                    Just (O.Mask _ m) -> m
          v1' = v1 .&. m1 .&. m2
          v2' = v2 .&. m1 .&. m2
          m' = if m1 .|. m2 == -1 then Nothing else Just (O.Mask w m1 .|. m2)
          v' = (v1 .&. m1) .|. (v2 .&. m2)

mkMatch :: O.Expr -> O.Expr -> [[O.Match]]
mkMatch e1 e2 | const1 && const2 && v1 == v2 = [[]]
              | const1 && const2 && v1 /= v2 = []
              | const1                       = mkMatch e2 e1
              | const2                       = O.Match f (slice2mask f sl) v2
              | otherwise                    = error $ "IR2OF.mkMatch: cannot match two variables: " ++ show e1 ++ " " ++ show e2
    where
    const1 = O.exprIsConst e1
    const2 = O.exprIsConst e2
    (O.EVal v1) = e1
    (O.EVal v2) = e2
    (O.EField f sl) = e1
    slice2mask :: O.Field -> Maybe (Int, Int) -> O.Mask
    slice2mask f msl = O.Mask (fieldWidth f) (bitRange $ maybe (fieldWidth f - 1, 0) id msl)
    bitRange (h,l) = foldl' (\a i -> setBit a i) (0::Integer) [l..h]

mkNext :: I.Pipeline -> I.Record -> I.Next -> O.Action
mkNext pl _ (I.Goto nd) = mkGoto pl nd
mkNext _  r (I.Send e)  = ActionOutput $ mkExpr r e
mkNext _  _ I.Drop      = O.ActionDrop

mkGoto :: I.Pipeline -> I.NodeId -> O.Action
mkGoto pl nd = 
    case G.lab nd pl of
         I.Fork{} -> O.ActionGroup nd
         _        -> O.ActionGoto nd 

-- New/delete port
--    Update the entry point table first
--    Then run normal table update

-- Delete switch

-- Table update
--    one of tables we care about?
--      yes: find all nodes that lookup or fork on this table




-- compute total order of nodes (map node ids to table numbers or
-- re-assign node numbers)

-- convert each node to a table:

-- Statically computed
-- * Par    -- all group, bucket per branch
-- * Cond   -- conditions to matches, indirect group for each branch

-- Dynamically updated
-- * First table that dispatches packet to the right pipeline
-- * Lookup -- encode table+constraint as OF table, BB to action list for each table entry
-- * Fork   -- precompute factorization into groups, action set per group

-- Merging ports
-- Switch role -> IR

-- Static pass:
-- IR -> OF program with empty table

-- Dynamic pass:
-- Relation update -> Switch ID -> OF program update
