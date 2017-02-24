{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

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
{-# LANGUAGE RecordWildCards, FlexibleContexts #-}

module NS(lookupType, checkType, getType,
          lookupFunc, checkFunc, getFunc,
          lookupVar, checkVar, getVar,
          --lookupLocalVar, checkLocalVar, getLocalVar,
          lookupRole, checkRole, getRole,
          lookupNode, checkNode, getNode,
          lookupConstructor, checkConstructor, getConstructor,
          lookupRelation, checkRelation, getRelation,
          ctxVars, ctxRels,
          isLVar, isLRel,
          --lookupBuiltin, checkBuiltin, getBuiltin,
          packetTypeName) where

import Data.List
import Control.Monad.Except
import Data.Maybe

import Syntax
import Name
import Util
import Pos
import Relation
import {-# SOURCE #-}Expr
import {-# SOURCE #-}Type
--import {-# SOURCE #-}Builtins

packetTypeName = "Packet"

lookupType :: Refine -> String -> Maybe TypeDef
lookupType Refine{..} n = find ((==n) . name) refineTypes

checkType :: (MonadError String me) => Pos -> Refine -> String -> me TypeDef
checkType p r n = case lookupType r n of
                       Nothing -> errR r p $ "Unknown type: " ++ n
                       Just t  -> return t

getType :: Refine -> String -> TypeDef
getType r n = fromJust $ lookupType r n


lookupFunc :: Refine -> String -> Maybe Function
lookupFunc Refine{..} n = find ((==n) . name) refineFuncs

checkFunc :: (MonadError String me) => Pos -> Refine -> String -> me Function
checkFunc p r n = case lookupFunc r n of
                       Nothing -> errR r p $ "Unknown function: " ++ n
                       Just f  -> return f

getFunc :: Refine -> String -> Function
getFunc r n = fromJust $ lookupFunc r n


lookupRole :: Refine -> String -> Maybe Role
lookupRole Refine{..} n = find ((==n) . name) refineRoles

checkRole :: (MonadError String me) => Pos -> Refine -> String -> me Role
checkRole p r n = case lookupRole r n of
                       Nothing -> errR r p $ "Unknown role: " ++ n
                       Just rl -> return rl

getRole :: Refine -> String -> Role
getRole r n = fromJust $ lookupRole r n

lookupVar :: Refine -> ECtx -> String -> Maybe Field
lookupVar r ctx n = fmap (\(Just t) -> Field nopos n t) 
                    $ lookup n $ (\(lvs, rvs) -> lvs ++ rvs) $ ctxVars r ctx

checkVar :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me Field
checkVar p r c n = case lookupVar r c n of
                        Nothing -> err p $ "Unknown variable: " ++ n-- ++ ". All known variables: " ++ (show $ (\(ls,vs) -> (map fst ls, map fst vs)) $ ctxVars r c)
                        Just v  -> return v

getVar :: Refine -> ECtx -> String -> Field
getVar r c n = fromJust $ lookupVar r c n

isGlobalVar :: Refine -> String -> Bool
isGlobalVar r v = isJust $ find ((==v) . name) $ refineState r

lookupNode :: Refine -> String -> Maybe Node
lookupNode Refine{..} n = find ((==n) . name) refineNodes

checkNode :: (MonadError String me) => Pos -> Refine -> String -> me Node
checkNode p r n = case lookupNode r n of
                        Nothing -> errR r p $ "Unknown switch: " ++ n
                        Just sw -> return sw

getNode :: Refine -> String -> Node
getNode r n = fromJust $ lookupNode r n

lookupConstructor :: Refine -> String -> Maybe Constructor
lookupConstructor r c = 
    find ((== c) . name) 
    $ concatMap (\td -> case tdefType td of       
                             Just (TStruct _ cs) -> cs
                             _                   -> [])
    $ refineTypes r 

checkConstructor :: (MonadError String me) => Pos -> Refine -> String -> me Constructor
checkConstructor p r c = case lookupConstructor r c of
                              Nothing   -> errR r p $ "Unknown constructor: " ++ c
                              Just cons -> return cons

getConstructor :: Refine -> String -> Constructor
getConstructor r c = fromJust $ lookupConstructor r c

lookupRelation :: Refine -> ECtx -> String -> Maybe Relation
lookupRelation r ctx n = find ((==n) . name) $ (\(rw,ro) -> rw ++ ro) $ ctxRels r ctx

checkRelation :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me Relation
checkRelation p r ctx n = case lookupRelation r ctx n of
                               Nothing  -> errR r p $ "Unknown relation: " ++ n -- ++ " in context " ++ show ctx
                               Just rel -> return rel

getRelation :: Refine -> ECtx -> String -> Relation
getRelation r ctx n = fromJust $ lookupRelation r ctx n

-- All variables available in the scope: (l-vars, read-only vars)
type MField = (String, Maybe Type)
f2mf f = (name f, Just $ fieldType f)

ctxVars :: Refine -> ECtx -> ([MField], [MField])
ctxVars r ctx = 
    case ctx of
         CtxRefine            -> (map f2mf $ refineState r, [])
         CtxRole rl           -> (plvars, (roleKey rl, Just $ relRecordType $ getRelation r CtxRefine $ roleTable rl) : prvars)
         CtxRoleGuard rl      -> ([], (roleKey rl, Just $ relRecordType $ getRelation r CtxRefine $ roleTable rl) : plvars ++ prvars)
         CtxFunc f _          -> let plvars' = filter (isGlobalVar r . fst) plvars 
                                     prvars' = filter (isGlobalVar r . fst) prvars in
                                 if funcPure f    
                                    then ([], map f2mf $ funcArgs f)
                                    else (plvars', (map f2mf $ funcArgs f) ++ prvars')
         CtxAssume a          -> ([], vartypes $ exprVars ctx $ assExpr a)
         CtxRelKey rel        -> ([], map f2mf $ relArgs rel)
         CtxRelForeign _ con  -> let ForeignKey _ _ fname _ = con 
                                     frel = getRelation r CtxRefine fname in
                                 ([], map f2mf $ relArgs frel)
         CtxCheck rel         -> ([], map f2mf $ relArgs rel)
         CtxRuleL _ rl _      -> ([], vartypes $ concatMap (exprVars ctx) $ ruleRHS rl)
         CtxRuleR _ rl        -> ([], vartypes $ concatMap (exprVars ctx) $ ruleRHS rl)
         CtxApply _ _ _       -> ([], plvars ++ prvars) -- disallow assignments inside arguments, cause we care about correctness
         CtxField _ _         -> (plvars, prvars)
         CtxLocation _ _      -> ([], plvars ++ prvars)
         CtxStruct _ _ _      -> (plvars, prvars)
         CtxTuple _ _ _       -> (plvars, prvars)
         CtxSlice  _ _        -> ([], plvars ++ prvars)
         CtxMatchExpr _ _     -> ([], plvars ++ prvars)
         CtxMatchPat _ _ _    -> ([], plvars ++ prvars)
         CtxMatchVal e pctx i -> let patternVars = map (mapSnd $ ctxExpectType r) $ exprVarDecls ctx $ fst $ (exprCases e) !! i in
                                 if isLExpr r pctx $ exprMatchExpr e
                                    then (plvars ++ patternVars, prvars)
                                    else (plvars, patternVars ++ prvars)
         CtxSeq1 _ _          -> (plvars, prvars)
         CtxSeq2 e pctx       -> let seq1vars = map (mapSnd $ ctxExpectType r) $ exprVarDecls (CtxSeq1 e pctx) $ exprLeft e
                                 in (plvars ++ seq1vars, prvars)
         CtxPar1 _ _          -> ([], plvars ++ prvars)
         CtxPar2 _ _          -> ([], plvars ++ prvars)
         CtxITEIf _ _         -> ([], plvars ++ prvars)
         CtxITEThen _ _       -> (plvars, prvars)
         CtxITEElse _ _       -> (plvars, prvars)
         CtxSetL _ _          -> (plvars, prvars)
         CtxSetR _ _          -> ([], plvars ++ prvars)
         CtxSend _ _          -> ([], plvars ++ prvars)
         CtxBinOpL _ _        -> ([], plvars ++ prvars)
         CtxBinOpR _ _        -> ([], plvars ++ prvars)
         CtxUnOp _ _          -> ([], plvars ++ prvars)
         CtxForkCond e _      -> ([], (frkvar e) : (plvars ++ prvars))
         CtxForkBody e pctx   -> if isLRel r pctx (exprTable e)
                                    then ([frkvar e], plvars ++ prvars)
                                    else ([], (frkvar e) : (plvars ++ prvars))
         CtxWithCond e _      -> ([], (frkvar e) : (plvars ++ prvars))
         CtxWithBody e pctx   -> if isLRel r pctx (exprTable e)
                                    then ((frkvar e):plvars, prvars)
                                    else (plvars, (frkvar e) : prvars)
         CtxWithDef _ _       -> (plvars, prvars)
         CtxAnyCond e _       -> ([], (frkvar e) : (plvars ++ prvars))
         CtxAnyBody e pctx    -> if isLRel r pctx (exprTable e)
                                    then ((frkvar e) : plvars, prvars)
                                    else (plvars, (frkvar e) : prvars)
         CtxAnyDef _ _        -> (plvars, prvars)
         CtxTyped _ _         -> (plvars, prvars)
         CtxRelPred _ _ _     -> ([], plvars ++ prvars)
    where (plvars, prvars) = ctxVars r $ ctxParent ctx 
          frkvar e = (exprFrkVar e, Just $ relRecordType $ getRelation r CtxRefine $ exprTable e)
          vartypes :: [(String, ECtx)] -> [MField]
          vartypes vs = map (\gr -> case filter (isJust . snd) $ map (mapSnd $ ctxExpectType r) gr of
                                         []  -> (fst $ head gr, Nothing)
                                         vs' -> head vs') 
                            $ sortAndGroup fst vs

-- Fork, with, any: relations become unavailable
-- Fork, Par: all relations become read-only
ctxRels :: Refine -> ECtx -> ([Relation], [Relation])
ctxRels r ctx = 
    case ctx of
         CtxRefine         -> partition relMutable $ refineRels r
         CtxRelKey _       -> ([],[])
         CtxRelForeign _ _ -> ([],[])
         CtxCheck _        -> ([],[])
         CtxPar1 _ _       -> ([], plrels ++ prrels)
         CtxPar2 _ _       -> ([], plrels ++ prrels)
         CtxForkCond _ _   -> ([], [])
         CtxForkBody e _   -> ([], del (exprTable e) $ plrels ++ prrels)
         CtxWithCond _ _   -> ([], [])
         CtxWithBody e _   -> (del (exprTable e) plrels, del (exprTable e) prrels)
         CtxAnyCond _ _    -> ([], [])
         CtxAnyBody e _    -> (del (exprTable e) plrels, del (exprTable e) prrels)
         _                 -> (plrels, prrels)
    where (plrels, prrels) = ctxRels r $ ctxParent ctx
          del t rels = filter ((/=t) . name) rels

{-
lookupBuiltin :: String -> Maybe Builtin
lookupBuiltin n = find ((==n) . name) builtins

checkBuiltin :: (MonadError String me) => Pos -> String -> me Builtin
checkBuiltin p n = case lookupBuiltin n of
                        Nothing -> err p $ "Unknown builtin: " ++ n
                        Just b  -> return b

getBuiltin :: String -> Builtin
getBuiltin n = fromJust $ lookupBuiltin n
-}
