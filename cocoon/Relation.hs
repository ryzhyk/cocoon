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

{-# LANGUAGE LambdaCase, RecordWildCards #-}

module Relation (relRecordType,
                 relGraph,
                 relTypes, 
                 relFuncsRec,
                 ruleIsRecursive) where

import qualified Data.Graph.Inductive as G
import Data.List
import Data.Maybe

import Util
import Name
import Syntax
import NS
import {-# SOURCE #-} Type
import {-# SOURCE #-} Expr

relRecordType :: Relation -> Type
relRecordType rel = tUser $ relName rel

relGraph :: Refine -> G.Gr String ()
relGraph r = foldl' (\g rel -> foldl' (\g' rname -> G.insEdge (relIdx $ name rel, relIdx rname, ()) g') g 
                               $ filter ((name rel) /=) $ relDeps rel) g0 
             $ refineRels r
    where g0 = G.insNodes (mapIdx (\rel i -> (i, name rel)) $ refineRels r) G.empty
          relIdx rname = fromJust $ findIndex ((rname == ) . name) $ refineRels r

relDeps :: Relation -> [String]
relDeps Relation{..} = nub $ rdeps ++ fdeps
    where
    rdeps = maybe [] (nub . concatMap ruleDeps) relDef
    fdeps = mapMaybe (\case
                       ForeignKey _ _ rname _ -> Just rname
                       _                      -> Nothing)
                     relConstraints

ruleIsRecursive :: Relation -> Rule -> Bool
ruleIsRecursive rel rule = any (\case
                                 E (ERelPred _ rname _) -> rname == name rel
                                 _                      -> False) $ ruleRHS rule

ruleDeps :: Rule -> [String]
ruleDeps rule = nub $ mapMaybe (\case
                                E (ERelPred _ rname _) -> Just rname
                                _                      -> Nothing) $ ruleRHS rule

relFuncsRec :: Refine -> Relation -> [String]
relFuncsRec r rel = nub 
                    $ concatMap (\case
                                   Check _ c -> exprFuncsRec r c
                                   _         -> []) 
                    $ relConstraints rel

relTypes :: Refine -> Relation -> [Type]
relTypes r rel = nub $ relFuncTypes r rel ++ relTypes' r rel

relTypes' :: Refine -> Relation -> [Type]
relTypes' r rel = nub $ concatMap (typeSubtypesRec r . typ) $ relArgs rel

relFuncTypes :: Refine -> Relation -> [Type]
relFuncTypes r rel = nub 
                     $ concatMap (typeSubtypesRec r)
                     $ concatMap (\f -> funcType f : (map typ $ funcArgs f) ++ (maybe [] (exprTypes r (CtxFunc f CtxRefine)) $ funcDef f))
                     $ map (getFunc r) 
                     $ relFuncsRec r rel
