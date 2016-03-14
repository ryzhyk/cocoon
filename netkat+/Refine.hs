{-# LANGUAGE RecordWildCards #-}

module Refine(funcGraph) where

import Data.List
import Data.Maybe
import qualified Data.Graph.Inductive as G

import Expr
import Syntax
import Name

funcGraph :: Refine -> G.Gr String ()
funcGraph r@Refine{..} = 
    let g0 = foldl' (\g (i,f) -> G.insNode (i,name f) g)
                    G.empty $ zip [0..] refineFuncs in
    foldl' (\g (i,f) -> case funcDef f of
                             Nothing -> g
                             Just e  -> foldl' (\g' f' -> G.insEdge (i, fromJust $ findIndex ((f'==) . name) $ refineFuncs, ()) g') g (exprFuncs r e))
           g0 $ zip [0..] refineFuncs


