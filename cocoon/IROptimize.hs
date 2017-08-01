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


{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module IROptimize(optimize) where
 
import qualified Data.Graph.Inductive as G 
import qualified Data.Map as M
import Control.Monad.State
import Data.List
--import Debug.Trace
import Data.Maybe

import IR

optimize :: Pipeline -> Pipeline
optimize pl | modified  = optimize pl'
            | otherwise = pl'
    where (pl', modified) = runState (pass pl) False

-- one pass of the optimizer
pass :: Pipeline -> State Bool Pipeline
pass pl = do
    pl1 <- optStraightLine pl
    pl2 <- optUnusedAssigns pl1
    pl3 <- optUnusedVars pl2
    return pl3


-- Merge nodes that contain straight-line code with predecessors
optStraightLine :: Pipeline -> State Bool Pipeline
optStraightLine pl =
    foldM (\pl_ n -> case G.lab (plCFG pl_) n of
                          Just (Par [b]) -> do put True     
                                               return $ merge pl_ n b
                          _              -> return pl_) pl 
          $ filter (/= plEntryNode pl) 
          $ G.nodes (plCFG pl)

merge :: Pipeline -> G.Node -> BB -> Pipeline
merge pl@Pipeline{..} n (BB as nxt) = pl{plCFG = cfg'}
    where (Just (pre, _, _, suc), cfg1) = G.match n plCFG
          -- merge n into each predecessor
          cfg' = foldl' (\cfg_ p -> let (Just (pre', _, l, suc'), cfg2) = G.match p cfg_
                                        -- rewrite predecessor's label
                                        l' = mapBB (\bb@(BB as' nxt') -> if nxt' == Goto n then BB (as' ++ as) nxt else bb) l
                                        cfg3 = (pre', p, l', suc') G.& cfg2
                                    in -- insert edges to successors of n
                                       foldl' (\cfg4 s -> G.insEdge (p, s, Edge) $ G.delLEdge (p, s, Edge) cfg4) cfg3 $ map snd suc)
                        cfg1 $ map snd pre


-- Remove assignments whose LHS is never read in the future
optUnusedAssigns :: Pipeline -> State Bool Pipeline
optUnusedAssigns pl = do
    cfg' <- foldM nodeOptUnusedAssigns (plCFG pl) $ G.labNodes $ plCFG pl
    return pl{plCFG = cfg'}

nodeOptUnusedAssigns :: CFG -> (NodeId, Node) -> State Bool CFG
nodeOptUnusedAssigns cfg (i, node) = do
    node' <- case node of
                  Fork t vs b       -> (liftM $ Fork t vs) $ bbOptUnusedAssigns cfg i b
                  Lookup t vs th el -> (liftM2 $ Lookup t vs) (bbOptUnusedAssigns cfg i th) (bbOptUnusedAssigns cfg i el)
                  Cond cs           -> liftM Cond $ mapM (\(c,b) -> liftM (c,) $ bbOptUnusedAssigns cfg i b) cs
                  Par bs            -> liftM Par $ mapM (bbOptUnusedAssigns cfg i) bs
    let (Just (pre, _, _, suc), cfg_) = G.match i cfg
    return $ (pre, i, node', suc) G.& cfg_

bbOptUnusedAssigns :: CFG -> NodeId -> BB -> State Bool BB
bbOptUnusedAssigns cfg i (BB as nxt) = do
    as' <- mapM (\(a,as') -> actionOptUnusedAssigns cfg i a as') $ zip as (tail $ tails as)
    return $ BB (catMaybes as') nxt

actionOptUnusedAssigns :: CFG -> NodeId -> Action -> [Action] -> State Bool (Maybe Action)
actionOptUnusedAssigns _   _  a@APut{} _           = return $ Just a
actionOptUnusedAssigns _   _  a@ADelete{} _        = return $ Just a
actionOptUnusedAssigns cfg i a@(ASet e1 _) after | isNothing mvar = return $ Just a
                                                 | used           = return $ Just a
                                                 | otherwise      = return Nothing
    where mvar = var e1
          var (EVar x)       = Just x
          var (ESlice e _ _) = var e
          var _              = Nothing
          Just v = mvar
          used = any (elem v . actionRHSVars) after ||                                 -- is var used in after?
                 any (elem v . nodeRHSVars) (map (fromJust . G.lab cfg) $ G.dfs [i] cfg \\ [i]) -- is vars used in cfg?

nodeRHSVars :: Node -> [VarName]
nodeRHSVars (Fork _ vs b)       = nub $ vs ++ bbRHSVars b
nodeRHSVars (Lookup _ vs b1 b2) = nub $ vs ++ bbRHSVars b1 ++ bbRHSVars b2
nodeRHSVars (Cond cs)           = nub $ concatMap (\(c,b) -> exprVars c ++ bbRHSVars b) cs 
nodeRHSVars (Par bs)            = nub $ concatMap bbRHSVars bs

bbRHSVars :: BB -> [VarName]
bbRHSVars (BB as _) = nub $ concatMap actionRHSVars as

actionRHSVars :: Action -> [VarName]
actionRHSVars (ASet _ e2)   = exprVars e2
actionRHSVars (APut _ vs)   = nub $ concatMap exprVars vs
actionRHSVars (ADelete _ c) = exprVars c


-- Remove unused variables
optUnusedVars :: Pipeline -> State Bool Pipeline
optUnusedVars pl = do
    let used = nub $ concatMap nodeVars $ map snd $ G.labNodes $ plCFG pl
    let vars = M.keys $ plVars pl
    let unused = vars \\ used
    if null unused
       then return pl
       else do put True
               return $ foldl' removeVar pl unused

removeVar :: Pipeline -> VarName -> Pipeline
removeVar pl v = pl{plVars = M.delete v (plVars pl)}

--nodeRemoveVar :: VarName -> Node -> Node
--nodeRemoveVar v (Fork r vs b)       = Fork r vs $ bbRemoveVar v b
--nodeRemoveVar v (Lookup r vs b1 b2) = Lookup r vs (bbRemoveVar v b1) (bbRemoveVar v b2)
--nodeRemoveVar v (Cond cs)           = Cond $ map (\(e, b) -> (e, bbRemoveVar v b)) cs
--nodeRemoveVar v (Par bs)            = Par $ map (bbRemoveVar v) bs
--
--bbRemoveVar :: VarName -> BB -> BB
--bbRemoveVar v (BB as nxt) = BB (filter (not . actionAssignsVar v) as) nxt
--
--actionAssignsVar :: VarName -> Action -> Bool
--actionAssignsVar v (ASet e _) = trace (if res then (show e ++ " assigns " ++ v) else (show e ++ " does not assign " ++ v)) res
--    where isvslice (EVar v')       = v' == v
--          isvslice (ESlice e' _ _) = isvslice e'
--          isvslice _               = False
--          res = isvslice e
--actionAssignsVar _ _          = False

-- Optimizations: 
--     * eliminate unused variables (for example only a few vars returned by a query are used)
--     * variable elimination by substitution
--     * merging tables to eliminate some variables
--     * merge cascade of conditions
--     + merge sequence of basic blocks
--     * merge cascades of parallel blocks
