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


{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module IROptimize(optimize) where
 
import qualified Data.Graph.Inductive as G 
import Control.Monad.State
import Data.List

import IR

optimize :: Pipeline -> Pipeline
optimize pl | modified  = optimize pl'
            | otherwise = pl'
    where (pl', modified) = runState (pass pl) False

-- one pass of the optimizer
pass :: Pipeline -> State Bool Pipeline
pass pl = do
    pl1 <- optStraightLine pl
    return pl1


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

-- Optimizations: 
--     * eliminate unused variables (for example only a few vars returned by a query are used)
--     * variable elimination by substitution
--     * merging tables to eliminate some variables
--     * merge cascade of conditions
--     + merge sequence of basic blocks
--     * merge cascades of parallel blocks
