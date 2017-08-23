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


{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections, FlexibleContexts, LambdaCase #-}

module IR.Optimize(optimize) where
 
import qualified Data.Graph.Inductive as G 
import qualified Data.Map as M
import Control.Monad.State
import Data.List
import Data.Maybe
--import Debug.Trace
--import System.IO.Unsafe
--import Data.Text.Lazy (unpack)

import IR.IR

optimize :: Int -> Pipeline -> Pipeline
optimize p pl | modified  = optimize (p+1) pl'
              | otherwise = pl'
    where (pl', modified) = --trace(unsafePerformIO $ do {writeFile ("pass" ++ show p ++ ".dot") $ unpack $ cfgToDot $ plCFG pl; return ""}) $
                            --trace ("******** optimizer pass " ++ show p ++ " *********") $
                            runState (pass pl) False

-- one pass of the optimizer
pass :: Pipeline -> State Bool Pipeline
pass pl = do
    pl1 <- fixpoint pl (\pl_ -> do pl1_ <- optUnusedAssigns pl_
                                   pl2_ <- optUnusedVars pl1_
                                   optVarSubstitute pl2_)
    -- do these last, as they may duplicate code, breaking the variable
    -- substitution optimization
    pl2 <- fixpoint pl1 optMergeCond
    pl3 <- fixpoint pl2 optStraightLine
    return pl3

fixpoint :: a -> (a -> State Bool a) -> State Bool a
fixpoint x f = do
    x' <- f x
    modified <- get
    if modified 
       then do put False
               x'' <- fixpoint x' f 
               put True
               return x''
       else return x'


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
    let f :: CFGCtx -> State Bool (Maybe Action)
        f ctx = f' ctx (ctxAction (plCFG pl) ctx)
        f' ctx a@(ASet e1 _) | isNothing mvar = return $ Just a
                             | used           = return $ Just a
                             | otherwise      = do put True
                                                   return Nothing
            where mvar = var e1
                  var (EVar x)       = Just x
                  var (ESlice e _ _) = var e
                  var _              = Nothing
                  Just v = mvar
                  match ctx' = elem v $ ctxRHSVars (plCFG pl) ctx' 
                  abort ctx' = ctxAssignsFullVar (plCFG pl) v ctx'
                  used = not $ null $ ctxSearchForward (plCFG pl) ctx match abort
        f' _ a                              = return $ Just a
    cfg' <- cfgMapCtxM (\_ node -> return node) f (plCFG pl)
    return pl{plCFG = cfg'}

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

-- Substitute variable values
optVarSubstitute :: Pipeline -> State Bool Pipeline
optVarSubstitute pl@Pipeline{..} = do
    cfg' <- cfgMapCtxM (varSubstNode plCFG) (varSubstAction plCFG) plCFG
    return pl{plCFG = cfg'}

varSubstNode :: CFG -> NodeId -> Node -> State Bool Node
varSubstNode cfg nd node = do
    let -- variables that occur in the node
        vars = case node of
                    Fork{..}   -> nodeDeps
                    Lookup{..} -> nodeDeps
                    Cond{..}   -> nub $ concatMap (exprVars . fst) nodeConds
                    Par{}      -> []
        substs = mapMaybe (\v -> fmap (v,) $ findSubstitution cfg (CtxNode nd) v) vars
        -- apply substitutions
        node' = foldl' (\node_ (v, e) -> 
                         --trace ("substitute " ++ v ++  " with " ++ show e ++ "\n         at node " ++ show node) $
                         case node_ of
                              Fork{..}   -> node_{nodeDeps = (nodeDeps \\ [v]) `union` exprVars e, nodePL = plSubstVar v e nodePL}
                              Lookup{..} -> node_{nodeDeps = (nodeDeps \\ [v]) `union` exprVars e, nodePL = plSubstVar v e nodePL}
                              Cond{..}   -> node_{nodeConds = map (\(c,b) -> (exprSubstVar v e c, b)) nodeConds}
                              Par{}      -> error "IROptimize.varSubstNode Par") 
                       node substs
    when (not $ null substs) $ put True
    return node'

varSubstAction :: CFG -> CFGCtx -> State Bool (Maybe Action)
varSubstAction cfg ctx = do
    let act = ctxAction cfg ctx
        vars = actionRHSVars act
        substs = mapMaybe (\v -> fmap (v,) $ findSubstitution cfg ctx v) vars
        -- apply substitutions
        act' = foldl' (\act_ (v, e) -> 
                        --trace ("substitute " ++ v ++  " with " ++ show e ++ "\n         in action " ++ show act) $
                        case act_ of
                             ASet     l r  -> ASet l $ exprSubstVar v e r
                             APut     t es -> APut t $ map (exprSubstVar v e) es
                             ADelete  t c  -> ADelete t $ exprSubstVar v e c)
                       act substs
    when (not $ null substs) $ put True
    return $ Just act'

findSubstitution :: CFG -> CFGCtx -> String -> Maybe Expr
findSubstitution cfg ctx v = 
    -- first pass search for a unique predecessor node that assigns v
    case ctxSearchBackward cfg ctx match1 abort1 of
         [ctx'] -> let ASet _ r = ctxAction cfg ctx'
                       as = exprAtoms r 
                       iscol ECol{} = True 
                       iscol _      = False in
                   -- if as contain column names, only allow substitutions within node
                   if any iscol as && ctxNode ctx' /= ctxNode ctx
                      then Nothing
                      else -- search for intermediate assignements to variables in r
                           case ctxSearchBackward cfg ctx (match2 as) (abort2 ctx') of
                                []                      -> Just r
                                [ctx''] | ctx'' == ctx' -> Just r
                                _                       -> Nothing
         _     -> Nothing
    where
    match1 CtxNode{} = False
    match1 ctx_ = ctxAssignsFullVar cfg v ctx_

    abort1 _ = False

    match2 _  CtxNode{} = False
    match2 as ctx_ = case ctxAction cfg ctx_ of
                          ASet l _ | (not $ null $ exprAtoms l `intersect` as) -> True
                          _                    -> False
    abort2 ctx' ctx_ = ctx' == ctx_

-- Merge cascades of cond nodes
optMergeCond :: Pipeline -> State Bool Pipeline
optMergeCond pl@Pipeline{..} = do
    cfg' <- foldM (\cfg_ n -> 
                    case G.lab cfg_ n of
                         -- conditional node
                         Just (Cond cs) -> case G.match n cfg_ of
                                                -- unique predecessor that is also a conditional node...
                                                (Just ([(_, n')], _, _, _), _) -> 
                                                    case G.lab cfg_ n' of
                                                         Just (Cond cs') -> do
                                                             -- and does not modify variables n depends on
                                                             let vs = concatMap (exprAtoms . fst) cs
                                                                 vs' = concatMap (bbLHSAtoms . snd) 
                                                                       $ filter ((==Goto n) . bbNext . snd) cs'
                                                             if null $ vs `intersect` vs'
                                                                then do put True     
                                                                        return $ mergeCond cfg_ n' n
                                                                else return cfg_
                                                         _ -> return cfg_
                                                _ -> return cfg_
                         _              -> return cfg_) plCFG
          $ G.nodes plCFG
    return $ pl{plCFG = cfg'}

bbLHSAtoms :: BB -> [Expr]
bbLHSAtoms b = nub $ concatMap (\case
                                 ASet l _ -> exprAtoms l
                                 _        -> []) $ bbActions b

mergeCond :: CFG -> NodeId -> NodeId -> CFG
mergeCond cfg nto n = (pre', nto, Cond csto', suc' ++ suc) G.& cfg2 
    where -- remove the node being merged
          (Just (_, _, Cond cs, suc), cfg1) = G.match n cfg
          (Just (pre', _, Cond csto, suc'), cfg2) = G.match nto cfg1
          csto' = concatMap (\(c', b') -> if bbNext b' /= Goto n
                                             then [(c',b')]
                                             else map (\(c,b) -> (conj[c', c], BB (bbActions b' ++ bbActions b) (bbNext b))) cs) csto
          
-- Optimizations: 
--     + eliminate unused variables (for example only a few vars returned by a query are used)
--     + variable elimination by substitution
--     * merging tables to eliminate some variables
--     + merge cascade of conditions
--     + merge sequence of basic blocks
--     * merge cascades of parallel blocks
