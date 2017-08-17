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

module OpenFlow.IR2OF( buildSwitch
                     , updateSwitch) where

import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Query.DFS as G
import qualified Data.Map                       as M

import qualified IR         as I
import qualified Compile2IR as I
import qualified OpenFlow   as O
import qualified Syntax     as C -- Cocoon

type IRSwitch = [(String, I.Pipeline)]
type IRSwitches = M.Map String IRSwitch

-- Uniquely identify an instance of the switch:
-- (SwitchRelation, primary key)
type SwitchId = (String, Integer)

type Record = M.Map I.ColName I.Expr

fieldMap :: M.Map I.FieldName O.Field

-- For each switch table
--  Compute and compile all port roles
precompile :: Refine -> IRSwitches
precompile r = M.fromList 
               $ map (\rel -> (name rel, assignTables $ I.compileSwitch r rel)) 
               $ filter (C.relIsSwitch r) $ C.refineRels r

-- Relabel port CFGs into openflow table numbers
assignTables :: IRSwitch -> IRSwitch
assignTables pls = foldl' (\(start, pls') pl -> let (start', pl') = relabel start pl
                                                in (start', pls' ++ [pl'])) (1, pls) pls
    where 
    relabel :: Int -> I.Pipeline -> (Int, I.Pipeline)
    relabel start pl = (start + length ordered, pl{I.plCFG = cfg', I.plEntryNode = start})
        where
        ordered = topsort $ I.plCFG pl
        rename nd = (fromJust $ findIndex (nd==) ordered) + start
        bbrename (I.BB as (I.Goto nd)) = I.BB as $ I.Goto rename nd
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
type Delta = M.Map String [(Bool, C.Expr)]
type DB    = M.Map String [C.Expr]

-- TODO backend-independent update procedure:
-- read all deltas in one transaction
-- update each switch from deltas
-- update realized state

-- New switch event
--   Store the list of tables this switch depends on
buildSwitch :: IRSwitch -> DB -> Integer -> [O.Command]
buildSwitch ports db swid = table0 : (staticcmds ++ updcmds)
    where
    table0 = O.AddFlow 0 $ O.Flow 0 [] [O.ActionDrop]
    -- Configure static part of the pipeline
    staticcmds = concatMap (\(_, pl) -> concatMap mkNode $ G.labNodes $ I.plCFG pl) ports
    -- Configure dynamic part from primary tables
    updcmds = updateSwitch (M.map (map (True,)) db) ports

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
    (add, del) = partition fst $ filter (\(pol, f) -> factField f "switch" == i) $ db M.! prel
    match f = mkCond $ I.EBinOp Eq (I.EPktField portnum) (factField f "portnum")
    delcmd = map (\(_,f) -> O.DelFlow 0 1 $ match f) del
    addcmd = map (\(_,f) -> O.AddFlow 0 $ O.Flow 1 (match f) [mkGoto pl $ I.plEntryNode]) del

mkNode :: (I.NodeId, I.Node) -> [O.Command]
mkNode (nd, node) = 
    case node of
         I.Par bs               -> [ O.AddGroup $ O.Group nd O.GroupAll $ map (O.Bucket Nothing . mkStaticBB) bs 
                                   , O.AddFlow nd $ O.Flow 0 [] [O.ActionGroup nd] ]
         I.Cond cs              -> concatMap (\(c,b) -> map (\m -> O.AddFlow nd $ O.Flow 0 m (mkStaticBB b)) $ mkCond c) cs
         I.Lookup t vs pl th el -> [O.AddFlow nd $ O.Flow 0 [] $ mkStaticBB el]
         I.Fork t vs pl b       -> [O.AddGroup $ O.Group nd O.GroupAll []]

updateNode :: Delta -> Pipeline -> (I.NodeId, I.Node) -> [O.Command]
updateNode db (nd, node) portpl = 
    case node of
         I.Par bs               -> []
         I.Cond cs              -> []
         I.Lookup t vs pl th el -> let (add, del) = partition fst (db M.! t) 
                                       delcmd = map (\(_,f) -> let O.Flow{..} = mkLookupFlow t f pl th
                                                               in O.DelFlow nd 1 flowPriority flowMatch) del
                                       addcmd = map (\(_,f) -> O.AddFlow nd 1 $ mkLookupFlow t f pl th) add
                                   in delcmd ++ addcmd
         I.Fork t vs _ b        -> -- create a bucket for each table row
                                   let (add, del) = partition fst (db M.! t) 
                                       map (\(_,f) -> O.DelBucket nd $ getBucketId t f) del
                                       map (\(_,f) -> O.AddBucket nd $ O.Bucket (Just $ getBucketId t f) $ mkBB portpl f b) add
                                   in delcmd ++ addcmd

getBucketId :: String -> Expr -> BucketId

mkStaticBB :: I.Pipeline -> I.BB -> [O.Action]
mkStaticBB pl b = mkBB pl (error "IR2OF.mkStaticBB requesting field value") b

mkBB :: I.Pipeline -> C.Expr -> I.BB -> [O.Action]
mkBB pl val (I.BB as n) = map (mkAction rec) as ++ [mkNext pl rec n]
    where rec = val2Record val
    
mkAction :: Record -> I.Action -> O.Action
mkAction val (I.ASet e1 e2) = O.ActionSet (mkExpr val e1) (mkExpr val e2)
mkAction _   a              = error $ "not implemented: IR2OF.mkAction" ++ show a

mkExpr :: Record -> I.Expr -> O.Expr
mkExpr val e = 
    case e of
         I.EPktField f     -> case fieldMap M.! f of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown field: " ++ show f
                                   Just f' -> O.EField f' 
         I.EVar      v     -> O.EField $ Register v
         I.ECol      c     -> case val M.! c of
                                   Nothing -> error $ "IR2OF.mkExpr: unknown column: " ++ show c
                                   Just v  -> mkExpr val v
         I.ESlice    x h l -> slice (mkExpr val x) h l
         I.EBit      w v   -> O.EVal $ O.ValInt w v
         _                 -> error $ "Not implemented: IR2OF.mkExpr " ++ show e


mkLookupFlow :: I.Pipeline -> String -> C.Expr -> I.Pipeline -> I.BB -> [Flow]
mkLookupFlow pl val lpl b = map (\m -> O.Flow 1 m as) matches
    where
    matches = mkPLMatch lpl val
    as = mkBB pl val b
    

mkCond :: I.Expr -> [[Match]]

const == v[h:l]
v[h:l] == const
v[h:l] == v'[...]
a || b   --> a ; b
a && b   --> a x b
not a    -->

            EPktField FieldName
          | EVar      VarName
          | ECol      ColName
          | ESlice    Expr Int Int

          | EBool     Bool
          | EBit      Int Integer
          | EBinOp    BOp Expr Expr
          | EUnOp     UOp Expr

mkPLMatch :: I.Pipeline -> C.Expr -> [[Match]]

mkNext :: I.Pipeline -> Record -> I.Next -> O.Action
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
