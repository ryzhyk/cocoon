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
import qualified Data.Graph.Inductive as G
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


relValidate :: (MonadError String me) => Refine -> Relation -> me ()
relValidate = error "relValidate is undefined"

stateValidate :: (MonadError String me) => Refine -> Field -> me ()
stateValidate = error "stateValidate is undefined"

roleValidate :: (MonadError String me) => Refine -> Role -> me ()
roleValidate = error "roleValidate is undefined"

{-
roleValidate r role@Role{..} = do
    uniqNames (\k -> "Multiple definitions of key " ++ k) roleKeys
    uniqNames (\v -> "Multiple definitions of local variable " ++ v) $ roleLocals role
    uniqNames (\v -> "Multiple definitions of fork variable " ++ v) $ roleForkVars role
    mapM_ (typeValidate r . fieldType) roleKeys
    exprValidate r (CtxRole role) [] roleKeyRange
    exprValidate r (CtxRole role) [] rolePktGuard
    _ <- statValidate r (CtxRole role) [] [] roleBody
    return ()
-}

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
                          exprTraverseTypeM r (\_ e' -> exprValidate2 r e') ctx e
                          --exprTraverseCtxM (exprValidate3 r) ctx e

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

checkNoVar :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me ()
checkNoVar p r ctx v = assertR r (isNothing $ lookupVar r ctx v) p 
                                 $ "Variable " ++ v ++ " already defined in this scope"

-- Traverse again with types
exprValidate2 :: (MonadError String me) => Refine -> ExprNode Type -> me ()
exprValidate2 r (EField p e f)      = case e of
                                           t@(TStruct _ _) -> assertR r (isJust $ find ((==f) . name) $ structArgs t) p
                                                                      $ "Unknown field " ++ f
                                           _               -> errR r (pos e) $ "Expression is not a struct"
exprValidate2 r (ESlice p e h l)    = case e of
                                           TBit _ w -> do assertR r (h >= l) p "Upper bound of the slice must be greater than lower bound"
                                                          assertR r (h < w) p "Upper bound of the slice cannot exceed argument width"
                                           _        -> errR r (pos e) $ "Expression is not a bit vector"
exprValidate2 r (EMatch _ _ cs)     = let t = snd $ head cs in
                                      mapM_ (matchType r t . snd) $ tail cs
exprValidate2 r (ESeq _ e1 e2)      = assertR r (e1 /= tSink) (pos e2) $ "Expression appears after a sink expression"
--EBinOp - ?
exprValidate2 r (EITE _ _ t me)     = maybe (return ()) (matchType r t) me
exprValidate2 _ _                   = return ()

-- Traverse again, check that every expression matches its expected type, if any

isLExpr :: Refine -> ECtx -> Expr -> Bool
isLExpr r ctx e = exprFoldCtx (isLExpr' r) ctx e

checkLExpr :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
checkLExpr r ctx e = assertR r (isLExpr r ctx e) (pos e) "Expression is not an l-value"

isLExpr' :: Refine -> ECtx -> ExprNode Bool -> Bool
isLExpr' r ctx (EVar _ v)       = isLVar r ctx v
isLExpr' _ _   (EPacket _)      = True
isLExpr' _ _   (EField _ e _)   = e
isLExpr' _ _   (ETuple _ as)    = and as
isLExpr' _ _   (EStruct _ _ as) = and as
isLExpr' _ _   (EVarDecl _ _)   = True
isLExpr' _ _   (EPHolder _)     = True
isLExpr' _ _   (ETyped _ e _)   = e
isLExpr' _ _   _                = False

isLVar :: Refine -> ECtx -> String -> Bool
isLVar r ctx v = elem v $ fst $ ctxVars r ctx

-- All variables available in the scope (l-vars, w)
ctxVars :: Refine -> ECtx -> ([String], [String])
ctxVars r ctx = 
    case ctx of
         CtxRefine            -> (map name $ refineState r, [])
         CtxRole rl           -> (plvars, (roleKey rl) : prvars)
         CtxFunc f            -> if funcPure f    
                                    then ([], map name $ funcArgs f)
                                    else (plvars, (map name $ funcArgs f) ++ prvars)
         CtxAssume a          -> ([], exprVars $ assExpr a)
         CtxRelation rel      -> ([], map name $ relArgs rel)
         CtxRule rl           -> ([], nub $ concatMap exprVars $ ruleRHS rl)
         CtxApply _ _ _       -> ([], plvars ++ prvars) -- disallow assignments inside arguments, cause we care about correctness
         CtxField _ _         -> (plvars, prvars)
         CtxLocation _ _      -> ([], plvars ++ prvars)
         CtxStruct _ _ _      -> ([], plvars ++ prvars)
         CtxTuple _ _ _       -> ([], plvars ++ prvars)
         CtxSlice  _ _        -> ([], plvars ++ prvars)
         CtxMatchExpr _ _     -> ([], plvars ++ prvars)
         CtxMatchPat _ _ _    -> ([], plvars ++ prvars)
         CtxMatchVal e pctx i -> let patternVars = exprVarDecls $ fst $ (exprCases e) !! i in
                                 if isLExpr r pctx $ exprMatchExpr e
                                    then (plvars ++ patternVars, prvars)
                                    else (plvars, patternVars ++ prvars)
         CtxSeq1 _ _          -> (plvars, prvars)
         CtxSeq2 e _          -> let seq1vars = exprVarDecls $ exprLeft e
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
         CtxForkCond e _      -> ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxForkBody e pctx   -> if isLRel r pctx (exprTable e)
                                    then ([exprFrkVar e], plvars ++ prvars)
                                    else ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxWithCond e _      -> ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxWithBody e pctx   -> if isLRel r pctx (exprTable e)
                                    then ([exprFrkVar e], plvars ++ prvars)
                                    else ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxWithDef _ _       -> (plvars, prvars)
         CtxAnyCond e _       -> ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxAnyBody e pctx    -> if isLRel r pctx (exprTable e)
                                    then ([exprFrkVar e], plvars ++ prvars)
                                    else ([], (exprFrkVar e) : (plvars ++ prvars))
         CtxAnyDef _ _        -> (plvars, prvars)
         CtxTyped _ _         -> (plvars, prvars)
    where (plvars, prvars) = ctxVars r $ ctxParent ctx 


isLRel :: Refine -> ECtx -> String -> Bool
isLRel r ctx rel = elem rel $ fst $ ctxRels r ctx

-- Fork, with, any: relations become unavailable
-- Fork, Par: all relations become read-only
ctxRels :: Refine -> ECtx -> ([String], [String])
ctxRels r ctx = 
    case ctx of
         CtxRefine       -> (\(rw,ro) -> (map name rw, map name ro)) $ partition relMutable $ refineRels r
         CtxPar1 _ _     -> ([], plrels ++ prrels)
         CtxPar2 _ _     -> ([], plrels ++ prrels)
         CtxForkCond _ _ -> ([], [])
         CtxForkBody e _ -> ([], delete (exprTable e) $ plrels ++ prrels)
         CtxWithCond _ _ -> ([], [])
         CtxWithBody e _ -> (delete (exprTable e) plrels, delete (exprTable e) prrels)
         CtxAnyCond _ _  -> ([], [])
         CtxAnyBody e _  -> (delete (exprTable e) plrels, delete (exprTable e) prrels)
         _               -> (plrels, prrels)
    where (plrels, prrels) = ctxRels r $ ctxParent ctx

ctxCheckSideEffects :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckSideEffects = error "ctxCheckSideEffects is undefined"

structArgs :: Type -> [Field]
structArgs (TStruct _ cs) = nub $ concatMap consArgs cs
structArgs t              = error $ "structArgs " ++ show t

{-
exprValidate r ctx vset (EVar p v) | isRoleCtx ctx =
    if elem v vset
       then return ()
       else case find ((==v) . name) $ roleKeys (ctxRole ctx) ++ ctxForkVars ctx of
                 Nothing -> errR r p $ "Unknown variable: " ++ v
                 Just _  -> return ()
exprValidate _ ctx _ (EVar p v) = do
   _ <- checkVar p ctx v
   return ()
exprValidate r ctx _ (EDotVar p v) = 
   case ctx of
        CtxSend _ t -> do _ <- checkKey p t v
                          return()
        _           -> errR r p "Dot-variable is not allowed here"
exprValidate r ctx _ (EPacket p) = do 
   case ctx of
        CtxAssume _ -> errR r p "Assumptions cannot refer to pkt"
        CtxFunc _   -> errR r p "Functions cannot refer to pkt"
        CtxRole _   -> return ()
        CtxSend _ _ -> return ()
        CtxFork _ _ -> return ()
   return ()
exprValidate r ctx vset (EApply p f as) = do
    func <- checkFunc p r f
    assertR r ((length $ funcArgs func) == length as) p "Number of arguments does not match function declaration"
    mapM_ (\(formal,actual) -> do exprValidate r ctx vset actual
                                  matchType r ctx actual formal) 
          $ zip (funcArgs func) as
exprValidate r ctx vset (EBuiltin p f as) = do
    func <- checkBuiltin p f
    mapM_ (exprValidate r ctx vset) as
    (bfuncValidate func) r ctx p as

exprValidate r ctx vset (EField p s f) = do
    exprValidate r ctx vset s
    case typ' r ctx s of
        TStruct _ fs -> assertR r (isJust $ find ((==f) . fieldName) fs) p $ "Unknown field " ++ f
        _            -> err p $ "Expression is not of struct type"

exprValidate r ctx vset (ELocation p rname as) = do
    role' <- checkRole p r rname
    assertR r ((length $ roleKeys role') == length as) p "Number of keys does not match role declaration"
    mapM_ (\(formal,actual) -> do exprValidate r ctx vset actual
                                  matchType r ctx actual formal) 
          $ zip (roleKeys role') as

exprValidate r ctx vset (EStruct p n as) = do
    t <- checkType p r n
    case typ' r ctx (tdefType t) of
         TStruct _ fs -> do assertR r (length as == length fs) p "Number of fields does not match struct definition"
                            mapM_ (\(field, e) -> do exprValidate r ctx vset e
                                                     matchType r ctx e field)
                                  $ zip fs as
         _            -> err p $ n ++ " is not a struct type"
exprValidate r ctx vset (EBinOp _ op left right) = do
    exprValidate r ctx vset left
    exprValidate r ctx vset right
    if' (elem op [Eq, Neq]) (matchType r ctx left right)
     $ if' (elem op [Lt, Lte, Gt, Gte, Plus, Minus, ShiftL, ShiftR]) (
          do assertR r (isUInt r ctx left)  (pos left)  $ "Not an integer expression"
             assertR r (isUInt r ctx right) (pos right) $ "Not an integer expression"
             matchType r ctx left right)
     $ if' (elem op [And, Or, Impl]) (
          do assertR r (isBool r ctx left)  (pos left)  $ "Not a Boolean expression"
             assertR r (isBool r ctx right) (pos right) $ "Not a Boolean expression")
     $ if' (elem op [Mod, Concat]) (
          do assertR r (isUInt r ctx left)  (pos left)  $ "Not an integer expression"
             assertR r (isUInt r ctx right) (pos right) $ "Not an integer expression") 
     $ undefined

exprValidate r ctx vset (EUnOp _ op e) = do
    exprValidate r ctx vset e
    case op of
         Not -> assertR r (isBool r ctx e) (pos e)  $ "Not a Boolean expression"

exprValidate r ctx vset (ESlice p e h l) = do
    exprValidate r ctx vset e
    case typ' r ctx e of
         TUInt _ w -> do assertR r (h >= l) p "Upper bound of the slice must be greater than lower bound"
                         assertR r (h < w) p "Upper bound of the slice cannot exceed argument width"
         _         -> errR r (pos e) "Cannot take slice of a non-integer expression"

exprValidate r ctx vset (ECond _ cs def) = do
    exprValidate r ctx vset def
    mapM_ (\(cond, e)-> do exprValidate r ctx vset cond
                           exprValidate r ctx vset e
                           assertR r (isBool r ctx cond) (pos cond) $ "Not a Boolean expression"
                           matchType r ctx e def) cs

exprValidate _ _ _ _ = return ()


lexprValidate :: (MonadError String me) => Refine -> ECtx -> [Expr] -> [String] -> Expr -> me ()
lexprValidate r ctx mset vset e = do
    exprValidate r ctx vset e
    assertR r (isLExpr e) (pos e) "Not an l-value"
    checkNotModified r ctx mset e

isLExpr :: Expr -> Bool
isLExpr (EVar _ _)        = False
isLExpr (EDotVar _ _)     = False
isLExpr (EPacket _)       = True
isLExpr (EApply _ _ _)    = False
isLExpr (EBuiltin _ _ _)  = False
isLExpr (EField _ s _)    = isLExpr s
isLExpr (ELocation _ _ _) = False
isLExpr (EBool _ _)       = False
isLExpr (EInt _ _ _)      = False
isLExpr (EStruct _ _ _)   = False
isLExpr (EBinOp _ _ _ _)  = False
isLExpr (EUnOp _ _ _)     = False
isLExpr (ESlice _ _ _ _)  = False -- TODO: allow this
isLExpr (ECond _ _ _)     = False

-- Checks that no part of lvalue e is in the modified set mset
checkNotModified :: (MonadError String me) => Refine -> ECtx -> [Expr] -> Expr -> me ()
checkNotModified r ctx mset e = do
    let checkParent e' = do assert (not $ elem e' mset) (pos e') $ show e' ++ " has already been assigned"
                            case e' of
                                 EField _ p _ -> checkParent p
                                 _            -> return ()
    -- e and its ancestors are not in mset
    checkParent e
    -- recursively check children
    case typ' r ctx e of
         TStruct _ fs -> mapM_ (checkNotModified r ctx mset . EField nopos e . name) fs
         _            -> return()


statValidate :: (MonadError String me) => Refine -> ECtx -> [Expr] -> [String] -> Statement -> me (Bool, [Expr], [String])
statValidate r ctx mset vset (SSeq _ h t) = do
    (sends, mset', vset') <- statValidate r ctx mset vset h
    assertR r (not sends) (pos h) "Send/fork not allowed in the middle of a sequence"
    statValidate r ctx mset' vset' t

statValidate r ctx mset vset (SPar _ h t) = do
    (_, mset1, _) <- statValidate r ctx mset vset h
    (_, mset2, _) <- statValidate r ctx mset vset t
    return $ (True, union mset1 mset2, vset)

statValidate r ctx mset vset (SITE _ c t e) = do
    exprValidate r ctx vset c
    assertR r (isBool r ctx c) (pos c) "Condition must be a Boolean expression"
    (sends1, mset1, _) <- statValidate r ctx mset vset t
    (sends2, mset2, _) <- maybe (return (False,[],[])) (statValidate r ctx mset vset) e
    return $ (sends1 || sends2, union mset1 mset2, vset)

statValidate r ctx mset vset (STest _ c) = do
    exprValidate r ctx vset c
    assertR r (isBool r ctx c) (pos c) "Filter must be a Boolean expression"
    return (False, mset, vset)

statValidate r ctx mset vset (SSet _ lval rval) = do
    exprValidate r ctx vset rval
    lexprValidate r ctx mset vset lval
    matchType r ctx lval rval
    when (exprIsValidFlag lval) $ case rval of
                                       EBool _ _ -> return ()
                                       _         -> errR r (pos rval) $ "Not a Boolean constant"
    return (False, union [lval] mset, vset)

statValidate r ctx mset vset (SSend _ dst) = do
    exprValidate r ctx vset dst
    assertR r (isLocation r ctx dst) (pos dst) "Not a valid location"
    case dst of
         ELocation _ _ _ -> return ()
         _               -> errR r (pos dst)  "send destination must be of the form Role[args]"
    let ELocation p rl _ = dst
    assertR r (rl /= name (ctxRole ctx)) p "role cannot send to itself"
    return (True, mset, vset)

statValidate r ctx mset vset (SSendND p rl c) = do
    role' <- checkRole p r rl
    exprValidate r (CtxSend ctx role') vset c
    assertR r (isBool r (CtxSend ctx role') c) (pos c) "Condition must be a Boolean expression"
    assertR r (rl /= name (ctxRole ctx)) p "role cannot send to itself"
    return (True, mset, vset)

statValidate r ctx mset vset (SHavoc _ lval) = do
    lexprValidate r ctx mset vset lval
    return (False, union [lval] mset, vset)

statValidate r ctx mset vset (SAssume _ c) = do
    exprValidate r ctx vset c
    assertR r (isBool r ctx c) (pos c) "Assumption must be a Boolean expression"
    return (False, mset, vset)

statValidate r ctx mset vset (SLet p t n v) = do
    assertR r (not $ elem n $ map name $ roleKeys $ ctxRole ctx) p $ "Local variable name shadows key name"
    assertR r (not $ elem n $ vset) p $ "Local variable name shadows previously declared variable"
    assertR r (not $ elem n $ map name $ roleForkVars $ ctxRole ctx) p $ "Local variable name shadows fork variable"
    typeValidate r t
    exprValidate r ctx vset v
    matchType r ctx t v 
    return (False, mset, union [n] vset)

statValidate r ctx mset vset (SFork p vs c b) = do
    let ctx' = CtxFork ctx vs
    mapM_ (\v -> do typeValidate r $ fieldType v
                    assertR r (not $ elem (name v) $ map name $ roleKeys $ ctxRole ctx) p $ "Fork variable name shadows key name"
                    assertR r (not $ elem (name v) $ map name $ roleLocals $ ctxRole ctx) p $ "Fork variable name shadows local variable"
                    assertR r (not $ elem (name v) $ map name $ ctxForkVars ctx) p $ "Fork variable name shadows containing fork variable")
           vs
    uniqNames (\n -> "Multiple definitions of variable " ++ n) vs
    exprValidate r ctx' vset c
    assertR r (isBool r ctx' c) (pos c) "Fork condition must be a Boolean expression"
    (_, mset', vset') <- statValidate r ctx' mset vset b
    return (True, mset', vset')

-}
