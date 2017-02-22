{-
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

module Validate (validate) where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe
import Data.List

import Syntax
import NS
import Util
import Type
import Pos
import Name
import Expr
import Refine
--import Statement
--import Builtins

-- Validate spec.  Constructs a series of contexts, sequentially applying 
-- refinements from the spec, and validates each context separately.
validate :: (MonadError String me) => Spec -> me [Refine]
validate (Spec []) = err nopos "Empty spec"
validate (Spec (r:rs)) = do
    combined <- liftM reverse $ foldM (\(p:rs') new -> liftM (:p:rs') (combine p new)) [r] rs
    mapM_ validate1 combined
    validateFinal $ last combined
    return combined

-- Validate final refinement before generating topology from it
validateFinal :: (MonadError String me) => Refine -> me ()
validateFinal r = do
    {-mapM_ (\Role{..} -> mapM_ (\f -> assertR r (isJust $ funcDef $ getFunc r f) (pos roleKeyRange) $ "Key range expression depends on undefined function " ++ f) 
                        $ exprFuncsRec r roleKeyRange)
          $ refineRoles r-}
    case grCycle (funcGraph r) of
         Nothing -> return ()
         Just t  -> err (pos $ getFunc r $ snd $ head t) $ "Recursive function definition: " ++ (intercalate "->" $ map (name . snd) t)
    mapM_ (roleValidateFinal r) $ refineRoles r
    mapM_ (nodeValidateFinal r) $ refineNodes r
--    mapM_ (\rl -> (mapM_ (\f -> assertR r (isJust $ funcDef $ getFunc r f) (pos rl) $ "Output port behavior depends on undefined function " ++ f)) 
--                  $ statFuncsRec r $ roleBody rl)
--          $ concatMap (map (getRole r . snd) . nodePorts) 
--          $ refineNodes r

-- Apply definitions in new on top of prev.
combine :: (MonadError String me) => Refine -> Refine -> me Refine
combine prev new = do 
    prev' <- foldM (\r role -> do assertR r (isJust $ find ((==role) . roleName) (refineRoles r)) (pos new) 
                                          $ "Role " ++ role ++ " is undefined in this context"
                                  assertR r (isJust $ find ((==role) . roleName) (refineRoles new)) (pos new) 
                                          $ "Role " ++ role ++ " is not re-defined by the refinement"
                                  assertR r ((roleKey $ getRole prev role) == (roleKey $ getRole new role)) (pos new) 
                                          $ "Role " ++ role ++ " is re-defined with a different key"
                                  assertR r ((roleTable $ getRole prev role) == (roleTable $ getRole new role)) (pos new) 
                                          $ "Role " ++ role ++ " is re-defined over a different table"
                                  assertR r ((roleCond $ getRole prev role) == (roleCond $ getRole new role)) (pos new) 
                                          $ "Role " ++ role ++ " is re-defined with a different guard"
                                  assertR r ((rolePktGuard $ getRole prev role) == (rolePktGuard $ getRole new role)) (pos new) 
                                          $ "Role " ++ role ++ " is re-defined with a different packet guard"
                                  return r{refineRoles = filter ((/=role) . roleName) $ refineRoles r}) prev (refineTarget new)
    let types   = refineTypes prev'     ++ refineTypes new
        roles   = refineRoles prev'     ++ refineRoles new
        assumes = refineAssumes prev'   ++ refineAssumes new 
        nodes   = refineNodes prev'     ++ refineNodes new 
        stvars  = refineState prev'     ++ refineState new
        rels    = refineRels prev'      ++ refineRels new
    funcs <- mergeFuncs $ refineFuncs prev'  ++ refineFuncs new
    return $ Refine (pos new) (refineTarget new) types stvars funcs rels assumes roles nodes

mergeFuncs :: (MonadError String me) => [Function] -> me [Function]
mergeFuncs []     = return []
mergeFuncs (f:fs) = do
    case find ((== name f) . name) fs of
         Nothing -> liftM (f:) $ mergeFuncs fs
         Just f' -> do checkFRefinement f f'
                       mergeFuncs fs

-- check that f' has the same signature and domain as f, and f does not have a body
checkFRefinement :: (MonadError String me) => Function -> Function -> me ()
checkFRefinement f f' = do
    assert (funcArgs f == funcArgs f') (pos f') $ "Arguments of " ++ name f' ++ " do not match previous definition at " ++ spos f
    assert (funcType f == funcType f') (pos f') $ "Type of " ++ name f' ++ " do not match previous definition at " ++ spos f
    assert (isNothing $ funcDef f) (pos f') $ "Cannot re-define function " ++ name f' ++ " previously defined at " ++ spos f

-- construct dependency graph
--typeGraph :: Refine -> G.Gr TypeDef ()
--typeGraph _ = undefined

-- Validate refinement with previous definitions inlined
validate1 :: (MonadError String me) => Refine -> me ()
validate1 r@Refine{..} = do
    uniqNames (\n -> "Multiple definitions of role " ++ n) refineRoles
    uniqNames (\n -> "Multiple definitions of type " ++ n) refineTypes
    assertR r (isJust $ find ((==packetTypeName) . tdefName) refineTypes) (pos r) $ packetTypeName ++ " is undefined"
    uniqNames (\n -> "Multiple definitions of function " ++ n) refineFuncs
    uniqNames (\n -> "Multiple definitions of node " ++ n) refineNodes
    mapM_ (\rl -> assertR r ((not $ refineIsMulticast Nothing r (name rl)) || refineIsDeterministic Nothing r (name rl)) (pos r) $
                                "Role " ++ name rl ++ " is both non-deterministic and multicast.  This is not supported at the moment.")
          refineRoles
    mapM_ (maybe (return ()) (typeValidate r) . tdefType) refineTypes
    uniqNames (\c -> "Multiple definitions of constructor " ++ c) $ concatMap typeCons $ refineStructs r
    -- each role occurs at most once as a port
    uniq' (\_ -> (pos r)) id (++ " is mentioned twice as a port") $ concatMap (concatMap (\(i,o) -> [i,o]) . nodePorts) refineNodes
    -- TODO: check for cycles in the types graph - catch recursive type definitions
--    case grCycle (typeGraph r) of
--         Nothing -> return ()
--         Just t  -> err (pos $ snd $ head t) $ "Recursive type definition: " ++ (intercalate "->" $ map (name . snd) t)
    mapM_ (relValidate r)    refineRels
    mapM_ (relValidate2 r)   refineRels
    mapM_ (stateValidate r)  refineState
    mapM_ (funcValidate r)   refineFuncs
    mapM_ (roleValidate r)   refineRoles
    mapM_ (assumeValidate r) refineAssumes
    -- TODO: check for cycles in the locations graph
    mapM_ (nodeValidate r)   refineNodes

typeValidate :: (MonadError String me) => Refine -> Type -> me ()
typeValidate _ (TBit p w)     = assert (w>0) p "Integer width must be greater than 0"
typeValidate r (TStruct _ cs) = do uniqNames (\c -> "Multiple definitions of constructor " ++ c) cs
                                   mapM_ (consValidate r) cs
                                   mapM_ (\as -> mapM_ (\(a1, a2) -> assertR r (typ a1 == typ a2) (pos a2) $
                                                                     "Argument " ++ name a1 ++ " is re-declared with a different types. Previous declaration: " ++ (show $ pos a1)) 
                                                       $ zip as $ tail as)
                                           $ sortAndGroup name $ concatMap consArgs cs
typeValidate r (TUser   p n)  = do _ <- checkType p r n
                                   return ()
typeValidate _ _              = return ()

consValidate :: (MonadError String me) => Refine -> Constructor -> me ()
consValidate r Constructor{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) consArgs
    mapM_ (typeValidate r . fieldType) $ consArgs

funcValidate :: (MonadError String me) => Refine -> Function -> me ()
funcValidate r f@Function{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) funcArgs
    mapM_ (typeValidate r . fieldType) funcArgs
    typeValidate r funcType
    exprValidate r (CtxFunc f) funcDom
    case funcDef of
         Nothing  -> return ()
         Just def -> do exprValidate r (CtxFunc f) def
                        matchType r funcType (exprType r (CtxFunc f) def)

-- Relations are validated in two passes: the first pass validates
-- fields; the seconds pass validates constraints and rules.  This 
-- two-phase process is needed, as foreign key constraints refer to 
-- fields of other relations
relValidate :: (MonadError String me) => Refine -> Relation -> me ()
relValidate r Relation{..} = do 
    uniqNames (\a -> "Multiple definitions of column " ++ a) relArgs
    mapM_ (typeValidate r . fieldType) relArgs

relValidate2 :: (MonadError String me) => Refine -> Relation -> me ()
relValidate2 r rel@Relation{..} = do 
    mapM_ (constraintValidate r rel) relConstraints
    maybe (return ()) (mapM_ (ruleValidate r rel)) relDef

constraintValidate :: (MonadError String me) => Refine -> Relation -> Constraint ->  me ()
constraintValidate r rel Check{..} = exprValidate r (CtxCheck rel) constrCond

-- primary/foreign key/unique
constraintValidate r rel constr = do
    -- TODO: should all keys be different?
    mapM_ (exprValidate r (CtxRelKey rel)) $ constrFields constr
    case constr of 
          ForeignKey{..} -> do frel <- checkRelation (pos constr) r CtxRefine constrForeign
                               mapM_ (exprValidate r (CtxRelForeign rel constr)) constrFArgs
                               assertR r (length constrFArgs == length constrFields) (pos constr)
                                       $ "Number of foreign fields does not match the number of local fields"
                               mapM_ (\(e1,e2) -> do let t1 = exprType r (CtxRelKey rel) e1
                                                     let t2 = exprType r (CtxRelForeign rel constr) e2
                                                     matchType r t1 t2) $ zip constrFields constrFArgs
                               assertR r (relCheckKey frel constrFArgs) (pos constr)
                                       $ "Foreign fields do not form a primary or unique key"
          _              -> return () 

relCheckKey :: Relation -> [Expr] -> Bool
relCheckKey Relation{..} fs = isJust $ find check relConstraints
    where check (Unique _ fs')     = fs' == fs
          check (PrimaryKey _ fs') = fs' == fs
          check _                  = False

ruleValidate :: (MonadError String me) => Refine -> Relation -> Rule -> me ()
ruleValidate r rel@Relation{..} rl@Rule{..} = do
    assertR r (length ruleLHS == length relArgs) (pos rl)
            $ "Number of arguments in the left-hand-side of the rule does not match the number of fields in relation " ++ name rel
    mapIdxM_ (\e i -> exprValidate r (CtxRuleL rel rl i) e) ruleLHS
    mapM_ (exprValidate r (CtxRuleR rel rl)) ruleRHS

stateValidate :: (MonadError String me) => Refine -> Field -> me ()
stateValidate r = typeValidate r . fieldType

roleValidate :: (MonadError String me) => Refine -> Role -> me ()
roleValidate r rl@Role{..} = do checkNoVar rolePos r CtxRefine roleKey
                                rel <- checkRelation rolePos r (CtxRole rl) roleTable
                                assertR r (not $ relMutable rel) rolePos 
                                        $ "Mutable relation " ++ name rel ++ " cannot be used in role declaration"
                                exprValidate r (CtxRoleGuard rl) roleCond
                                exprValidate r (CtxRoleGuard rl) rolePktGuard
                                exprValidate r (CtxRole rl) roleBody

roleValidateFinal :: (MonadError String me) => Refine -> Role -> me ()
roleValidateFinal r Role{..} = do
    assert (exprIsDeterministic r roleBody) (pos roleBody) "Cannot synthesize non-deterministic behavior"
    return ()

assumeValidate :: (MonadError String me) => Refine -> Assume -> me ()
assumeValidate = error "assumeValidate is undefined"
{-
assumeValidate r a@Assume{..} = do
    uniqNames (\v -> "Multiple definitions of variable " ++ v) assVars
    mapM_ (typeValidate r . fieldType) assVars
    exprValidate r (CtxAssume a) [] assExpr
    assertR r (isBool r (CtxAssume a) assExpr) (pos assExpr) $ "Not a Boolean expression"
    return ()
-}

nodeValidate :: (MonadError String me) => Refine -> Node -> me ()
nodeValidate = error "nodeValidate is undefined"
{-
nodeValidate r nd@Node{..} = do
    nodeRole <- checkRole (pos nd) r nodeName
    -- for each port 
    mapM_ (\(p1,p2) -> do r1 <- checkRole (pos nd) r p1
                          r2 <- checkRole (pos nd) r p2
                          assertR r (roleKeys r1 == roleKeys r2) (pos nd) 
                                  $ "Input-output roles (" ++ p1 ++ "," ++ p2 ++ ") must have identical parameter lists"
                          assertR r (roleKeyRange r1 == roleKeyRange r2) (pos nd)
                                  $ "Input-output roles (" ++ p1 ++ "," ++ p2 ++ ") must have identical key ranges"
                          let validateR rl = do assertR r (length (roleKeys rl) > 0 && isUInt r (CtxRole rl) (last $ roleKeys rl)) (pos nd) 
                                                        $ "Port " ++ name rl ++ " must be indexed with an integer key"
                                                assertR r ((init $ roleKeys rl) == roleKeys nodeRole) (pos nd) 
                                                       $ "Port " ++ name rl ++ " must be indexed with the same keys as node " ++ nodeName ++ " and one extra integer key" 
                          validateR r1
                          validateR r2)
          nodePorts
-}

nodeValidateFinal :: (MonadError String me) => Refine -> Node -> me ()
nodeValidateFinal r nd@Node{..} = do
    -- for each port 
    mapM_ (\(p1,p2) -> do r1 <- checkRole (pos nd) r p1
                          r2 <- checkRole (pos nd) r p2
                          -- input ports can only send to output ports of the same node
                          assertR r (all (\(E (ELocation _ rl _)) -> (elem rl (map snd nodePorts)) {-&& 
                                                                    (all (\(key, arg) -> arg == (EVar nopos $ name key)) $ zip (init $ roleKeys r1) args)-})
                                         $ exprSendsTo r (roleBody r1)) (pos nd)
                                 $ "Inbound port " ++ p1 ++ " is only allowed to forward packets to the node's outbound ports"
                          assertR r (not $ any (\rl -> elem rl (map snd nodePorts)) $ exprSendsToRoles r (roleBody r2)) (pos nd)
                                 $ "Outbound port " ++ p2 ++ " is not allowed to forward packets to other outbound ports"
                          checkLinkExpr r $ roleBody r2)
          nodePorts


checkLinkExpr :: (MonadError String me) => Refine -> Expr -> me ()
checkLinkExpr r e = do checkLinkExpr' e
                       mapM_ (maybe (return ()) checkLinkExpr' . funcDef . getFunc r) $ exprFuncsRec r e


checkLinkExpr' :: (MonadError String me) => Expr -> me ()
checkLinkExpr' e = exprTraverseM (\e' -> case e' of
                                              EPar p _ _      -> err p "Parallel composition not allowed in output port body"
                                              EFork p _ _ _ _ -> err p "Fork not allowed in output port body"
                                              ESet p _ _      -> err p "Assignment not allowed in output port body"
                                              EPacket p       -> err p "Output port body may not inspect packet headers"
                                              _               -> return ()) e

exprValidate :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
exprValidate r ctx e = do exprTraverseCtxM (exprValidate1 r) ctx e
                          exprTraverseTypeME r (exprValidate2 r) ctx e

exprTraverseTypeME :: (MonadError String me) => Refine -> (ECtx -> ExprNode Type -> me ()) -> ECtx -> Expr -> me ()
exprTraverseTypeME r = exprTraverseCtxWithM (\ctx e -> do 
    e' <- exprMap (return . Just) e
    case exprType' r ctx e' of
         Just t  -> do case ctxExpectType r ctx of
                            Nothing -> return ()
                            Just t' -> assertR r (matchType' r t t') (pos e) 
                                               $ "Couldn't match expected type " ++ show t' ++ " with actual type " ++ show t
                       return t
         Nothing -> error $ "Expression " ++ show e ++ " has unknown type") 

-- This function does not perform type checking: just checks that all functions and
-- variables are defined; the number of arguments matches declarations, etc.
exprValidate1 :: (MonadError String me) => Refine -> ECtx -> ExprNode Expr -> me ()
exprValidate1 r ctx (EVar p v)          = do _ <- checkVar p r ctx v
                                             return ()
exprValidate1 r ctx (EPacket p)         = ctxCheckSideEffects p r ctx
exprValidate1 r _   (EApply p f as)     = do fun <- checkFunc p r f
                                             assertR r (length as == length (funcArgs fun)) p
                                                     $ "Number of arguments does not match function declaration"
exprValidate1 _ _   (EField _ _ _)      = return ()
exprValidate1 r _   (ELocation p rl _)  = do _ <- checkRole p r rl
                                             return ()
exprValidate1 _ _   (EBool _ _)         = return ()
exprValidate1 _ _   (EInt _ _)          = return ()
exprValidate1 _ _   (EString _ _)       = return ()
exprValidate1 _ _   (EBit _ _ _)        = return ()
exprValidate1 r _   (EStruct p c as)    = do cons <- checkConstructor p r c
                                             assertR r (length as == length (consArgs cons)) p
                                                     $ "Number of arguments does not match constructor declaration"
exprValidate1 _ _   (ETuple _ _)        = return ()
exprValidate1 _ _   (ESlice _ _ _ _)    = return ()
exprValidate1 _ _   (EMatch _ _ _)      = return ()
exprValidate1 r ctx (EVarDecl p v)      = checkNoVar p r ctx v
exprValidate1 _ _   (ESeq _ _ _)        = return ()
exprValidate1 r ctx (EPar p _ _)        = ctxCheckSideEffects p r ctx
exprValidate1 _ _   (EITE _ _ _ _)      = return ()
exprValidate1 r ctx (EDrop p)           = ctxCheckSideEffects p r ctx
exprValidate1 r ctx (ESet _ l _)        = checkLExpr r ctx l
exprValidate1 r ctx (ESend p _)         = ctxCheckSideEffects p r ctx
exprValidate1 _ _   (EBinOp _ _ _ _)    = return ()
exprValidate1 _ _   (EUnOp _ Not _)     = return ()
exprValidate1 r ctx (EFork p v t _ _)   = do ctxCheckSideEffects p r ctx
                                             _ <- checkRelation p r ctx t
                                             _ <- checkNoVar p r ctx v
                                             return ()
exprValidate1 r ctx (EWith p v t _ _ _) = do _ <- checkRelation p r ctx t
                                             _ <- checkNoVar p r ctx v
                                             return ()
exprValidate1 r ctx (EAny  p v t _ _ _) = do ctxCheckSideEffects p r ctx
                                             _ <- checkRelation p r ctx t
                                             _ <- checkNoVar p r ctx v
                                             return ()
exprValidate1 _ _   (EPHolder _)        = return ()
exprValidate1 _ _   (ETyped _ _ _)      = return ()
exprValidate1 r ctx (ERelPred p rel as) = do ctxCheckRelPred p r ctx
                                             rel' <- checkRelation p r ctx rel
                                             assertR r (length as == length (relArgs rel')) p
                                                     $ "Number of arguments does not match relation declaration"

checkNoVar :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me ()
checkNoVar p r ctx v = assertR r (isNothing $ lookupVar r ctx v) p 
                                 $ "Variable " ++ v ++ " already defined in this scope"

-- Traverse again with types.  This pass ensures that all sub-expressions
-- have well-defined types that match their context
exprValidate2 :: (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
exprValidate2 r _   (EField p e f)      = case e of
                                               t@(TStruct _ _) -> assertR r (isJust $ find ((==f) . name) $ structArgs t) p
                                                                          $ "Unknown field " ++ f
                                               _               -> errR r (pos e) $ "Expression is not a struct"
exprValidate2 r _   (ESlice p e h l)    = case e of
                                               TBit _ w -> do assertR r (h >= l) p 
                                                                      $ "Upper bound of the slice must be greater than lower bound"
                                                              assertR r (h < w) p
                                                                      $ "Upper bound of the slice cannot exceed argument width"
                                               _        -> errR r (pos e) $ "Expression is not a bit vector"
exprValidate2 r _   (EMatch _ _ cs)     = let t = snd $ head cs in
                                          mapM_ (matchType r t . snd) $ tail cs
                                          -- TODO: pattern structure matches 
exprValidate2 r _   (ESeq _ e1 e2)      = assertR r (e1 /= tSink) (pos e2) $ "Expression appears after a sink expression"
exprValidate2 r _   (EBinOp _ op e1 e2) = case op of 
                                               Eq     -> m
                                               Neq    -> m
                                               Lt     -> do {m; isint1}
                                               Gt     -> do {m; isint1}
                                               Lte    -> do {m; isint1}
                                               Gte    -> do {m; isint1}
                                               And    -> do {m; isbool}
                                               Or     -> do {m; isbool}
                                               Impl   -> do {m; isbool}
                                               Plus   -> do {m; isint1} 
                                               Minus  -> do {m; isint1}
                                               ShiftR -> do {isint1; isint2} 
                                               ShiftL -> do {isint1; isint2}
                                               Mod    -> do {isint1; isint2}
                                               Concat -> do {isbit1; isbit2}
    where m = matchType r e1 e2
          isint1 = assertR r (isInt r e1 || isBit r e1) (pos e1) $ "Not an integer"
          isint2 = assertR r (isInt r e2 || isBit r e2) (pos e2) $ "Not an integer"
          isbit1 = assertR r (isBit r e1) (pos e1) $ "Not a bit vector"
          isbit2 = assertR r (isBit r e2) (pos e2) $ "Not a bit vector"
          isbool = assertR r (isBool r e1) (pos e1) $ "Not a Boolean"
exprValidate2 r ctx (EVarDecl p _)      = assertR r (isJust $ ctxExpectType r ctx) p $ "Variable type is unknown"
exprValidate2 r _   (EITE _ _ t me)     = matchType r t $ maybe (tTuple []) id me
exprValidate2 _ _   _                   = return ()

checkLExpr :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
checkLExpr r ctx e = assertR r (isLExpr r ctx e) (pos e) "Expression is not an l-value"

ctxCheckSideEffects :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckSideEffects = error "ctxCheckSideEffects is undefined"

ctxCheckRelPred :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckRelPred = error "ctxCheckRelPred is undefined"

structArgs :: Type -> [Field]
structArgs (TStruct _ cs) = nub $ concatMap consArgs cs
structArgs t              = error $ "structArgs " ++ show t
