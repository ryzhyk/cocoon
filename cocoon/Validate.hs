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
{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

module Validate ( validate
                , exprValidate) where

import Control.Monad.Except
import Data.Maybe
import Data.List
-- import Debug.Trace

import Syntax
import NS
import Util
import Type
import Pos
import Name
import Expr
import Refine
import Relation
--import SQL
import Port
import {-# SOURCE #-} Builtins

{-
-- Validate spec.  Constructs a series of contexts, sequentially applying 
-- refinements from the spec, and validates each context separately.
validate :: (MonadError String me) => Spec -> me [Refine]
validate (Spec []) = err nopos "Empty spec"
validate (Spec (r:rs)) = do
    combined <- liftM reverse $ foldM (\(p:rs') new -> liftM (:p:rs') (combine p new)) [r] rs
    mapM_ validate1 combined
    validateFinal $ last combined
    return combined

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
                                  return r{refinePorts = filter ((/=role) . roleName) $ refineRoles r}) prev (refineTarget new)
    let types   = refineTypes prev'     ++ refineTypes new
        roles   = refineRoles prev'     ++ refineRoles new
        assumes = refineAssumes prev'   ++ refineAssumes new 
        stvars  = refineState prev'     ++ refineState new
        rels    = refineRels prev'      ++ refineRels new
    funcs <- mergeFuncs $ refineFuncs prev'  ++ refineFuncs new
    return $ Refine (pos new) (refineTarget new) types stvars funcs rels assumes roles

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
-}

-- Validate refinement with previous definitions inlined
validate :: (MonadError String me) => Refine -> me ()
validate r@Refine{..} = do
    uniqNames (\n -> "Multiple definitions of switch " ++ n) refineSwitches
    uniqNames (\n -> "Multiple definitions of port " ++ n) refinePorts
    uniqNames (\n -> "Multiple definitions of type " ++ n) refineTypes
    assertR r (isJust $ find ((==packetTypeName) . tdefName) refineTypes) (pos r) $ packetTypeName ++ " is undefined"
    uniqNames (\n -> "Multiple definitions of function " ++ n) refineFuncs
    uniqNames (\n -> "Multiple definitions of relation " ++ n) refineRels
    mapM_ (maybe (return ()) (typeValidate r) . tdefType) refineTypes
    uniqNames (\c -> "Multiple definitions of constructor " ++ c) $ concatMap typeCons $ refineStructs r
    -- each role occurs at most once as a port
    --uniq' (\_ -> (pos r)) id (++ " is mentioned twice as a port") $ concatMap (concatMap (\(i,o) -> [i,o]) . nodePorts) refineNodes
    mapM_ (relValidate r)    refineRels
    mapM_ (funcValidate1 r)  refineFuncs
    mapM_ (relValidate2 r)   refineRels
    maybe (return ()) 
          (\cyc -> errR r (pos $ getRelation r $ snd $ head cyc) 
                     $ "Dependency cycle among relations: " ++ (intercalate ", " $ map (name . snd) cyc))
          $ (grCycle $ relGraph r)
    mapM_ (stateValidate r)  refineState
    mapM_ (funcValidate2 r)  refineFuncs
    mapM_ (switchValidate r) refineSwitches
    mapM_ (portValidate r)   refinePorts
    mapM_ (assumeValidate r) refineAssumes
    mapM_ (relValidate3 r)   refineRels
    -- TODO: check for cycles in the locations graph
    --mapM_ (\rl -> assertR r ((not $ refineIsMulticast Nothing r (name rl)) || refineIsDeterministic Nothing r (name rl)) (pos r) $
    --                            "Role " ++ name rl ++ " is both non-deterministic and multicast.  This is not supported at the moment.")
    --      refineRoles
    validateFinal r

-- Validate final refinement before generating topology from it
validateFinal :: (MonadError String me) => Refine -> me ()
validateFinal r = do
    {-mapM_ (\Role{..} -> mapM_ (\f -> assertR r (isJust $ funcDef $ getFunc r f) (pos roleKeyRange) $ "Key range expression depends on undefined function " ++ f) 
                        $ exprFuncsRec r roleKeyRange)
          $ refineRoles r-}
    case grCycle (funcGraph r) of
         Nothing -> return ()
         Just t  -> err (pos $ getFunc r $ snd $ head t) $ "Recursive function definition: " ++ (intercalate "->" $ map (name . snd) t)
    mapM_ (portValidateFinal r) $ refinePorts r
    --mapM_ (nodeValidateFinal r) $ refineNodes r
--    mapM_ (\rl -> (mapM_ (\f -> assertR r (isJust $ funcDef $ getFunc r f) (pos rl) $ "Output port behavior depends on undefined function " ++ f)) 
--                  $ statFuncsRec r $ roleBody rl)
--          $ concatMap (map (getRole r . snd) . nodePorts) 
--          $ refineNodes r


typeValidate :: (MonadError String me) => Refine -> Type -> me ()
typeValidate _ (TBit p w)     = assert (w>0) p "Integer width must be greater than 0"
typeValidate r (TStruct _ cs) = do uniqNames (\c -> "Multiple definitions of constructor " ++ c) cs
                                   mapM_ (consValidate r) cs
                                   mapM_ (\as -> mapM_ (\(a1, a2) -> assertR r (typ a1 == typ a2) (pos a2) $
                                                                     "Argument " ++ name a1 ++ " is re-declared with a different types. Previous declaration: " ++ (show $ pos a1)) 
                                                       $ zip as $ tail as)
                                           $ sortAndGroup name $ concatMap consArgs cs
typeValidate r (TTuple _ ts)  = mapM_ (typeValidate r) ts
typeValidate r (TArray _ t _) = typeValidate r t
typeValidate r (TUser   p n)  = do _ <- checkType p r n
                                   return ()
typeValidate _ _              = return ()

consValidate :: (MonadError String me) => Refine -> Constructor -> me ()
consValidate r Constructor{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) consArgs
    mapM_ (typeValidate r . fieldType) $ consArgs

funcValidate1 :: (MonadError String me) => Refine -> Function -> me ()
funcValidate1 r Function{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) funcArgs
    mapM_ (typeValidate r . fieldType) funcArgs
    typeValidate r funcType

funcValidate2 :: (MonadError String me) => Refine -> Function -> me ()
funcValidate2 r f@Function{..} = do
    case funcDef of
         Nothing  -> return ()
         Just def -> exprValidate r (CtxFunc f CtxRefine) def



-- Relations are validated in two passes: the first pass validates
-- fields; the second pass validates constraints and rules.  This 
-- two-phase process is needed, as foreign key constraints refer to 
-- fields of other relations
relValidate :: (MonadError String me) => Refine -> Relation -> me ()
relValidate r Relation{..} = do 
    uniqNames (\a -> "Multiple definitions of column " ++ a) relArgs
    mapM_ (typeValidate r . fieldType) relArgs

relValidate2 :: (MonadError String me) => Refine -> Relation -> me ()
relValidate2 r rel@Relation{..} = do 
    assertR r ((length $ filter isPrimaryKey relConstraints) <= 1) relPos $ "Multiple primary keys are not allowed"
    mapM_ (constraintValidate r rel) relConstraints
    maybe (return ()) (mapM_ (ruleValidate r rel)) relDef
    maybe (return ()) (\rules -> assertR r (any (not . ruleIsRecursive rel) rules) relPos 
                                         "View must have at least one non-recursive rule") relDef

switchValidate :: (MonadError String me) => Refine -> Switch -> me ()
switchValidate r Switch{..} = do
    rel@Relation{..} <- checkRelation switchPos r CtxRefine switchRel
    assertR r (isJust $ relPrimaryKey rel) switchPos $ "Switch relation " ++ switchName ++ " must have a primary key" 
    assertR r ((length $ fromJust $ relPrimaryKey rel) == 1) switchPos
              $ "Switch relation " ++ switchName ++ " must have a primary key with a single column" 
    assertR r (isBit r $ exprType' r (CtxRelKey rel) $ head $ fromJust $ relPrimaryKey rel) switchPos
              $ "Switch relation " ++ switchName ++ " must have a primary key of type bit<N>" 
    assertR r (case find ((== "failed") . name) relArgs of
                    Nothing -> False
                    Just f  -> isBool r f) switchPos $ "Switch relation " ++ switchName ++ " must have a Boolean field named \"failed\"" 

portValidate :: (MonadError String me) => Refine -> SwitchPort -> me ()
portValidate r SwitchPort{..} = do 
     rel@Relation{..} <- checkRelation portPos r CtxRefine portRel
     infunc  <- checkFunc portPos r portIn
     moutfunc <- maybe (return Nothing) (liftM Just . checkFunc portPos r) portOut

     assertR r (isJust $ funcDef infunc) portPos 
               $ "Method " ++ name infunc ++ " used as input port handler must be defined"
     maybe (return())
           (\f -> assertR r (isJust $ funcDef f) portPos 
                          $ "Method " ++ name f ++ " used as output port handler must be defined")
           moutfunc

     assertR r (not $ funcPure infunc) portPos 
               $ "Method " ++ name infunc ++ " used as input port handler must be declared as procedure"
     maybe (return ())
           (\f -> assertR r (not $ funcPure f) portPos 
                          $ "Method " ++ name f ++ " used as output port handler must be declared as procedure")
           moutfunc
     assertR r ((1 == length (funcArgs infunc)) && 
                (relRecordType rel == (fieldType $ head (funcArgs infunc)))) portPos 
               $ "Method " ++ name infunc ++ " must take a single argument of type " ++ show (relRecordType rel)
     maybe (return ())
           (\f -> assertR r ((1 == length (funcArgs f)) && 
                             (relRecordType rel == (fieldType $ head (funcArgs f)))) portPos 
                            $ "Method " ++ name f ++ " must take a single argument of type " ++ show (relRecordType rel))
           moutfunc
     assertR r (tSink == funcType infunc) portPos 
               $ "Method " ++ name infunc ++ " used as input port handler must be declared as sink"
     maybe (return ())
           (\f -> assertR r (tSink == funcType f) portPos 
                          $ "Method " ++ name f ++ " used as output port handler must be declared as sink")
           moutfunc
     --assertR r (roleTable inrole == relName) p $ "Role " ++ inp ++ " is not indexed by the " ++ relName ++ " relation" 
     --assertR r (roleTable outrole == relName) p $ "Role " ++ outp ++ " is not indexed by the " ++ relName ++ " relation" 
     --assertR r (roleCond inrole == eTrue) p 
     --        $ "Role " ++ inp ++ " declared as switch port should not have a guard condition, but there is one specified at " ++ (show $ pos $ roleCond inrole)
     --assertR r (roleCond outrole == eTrue) p 
     --        $ "Role " ++ outp ++ " declared as switch port should not have a guard condition, but there is one specified at " ++ (show $ pos $ roleCond inrole)
     assertR r (isJust $ find ((== "switch") . name) relArgs) relPos
             $ "Port relation " ++ relName ++ " must have a column named \"switch\""
     maybe (errR r relPos "The \"switch\" column must be declared as foreign key")
           (\(ForeignKey p' _ n _) -> do let rel' = getRelation r n
                                         assertR r (relIsSwitch r rel') p' 
                                                 "The \"switch\" column must refer to a switch relation")
           $ find (\case 
                    ForeignKey _ [f] _ _ -> f == eVar "switch"
                    _                    -> False) relConstraints
     portnum <- maybe (errR r relPos $ "Port relation " ++ relName ++ " must have a column named \"portnum\"")
                      return
                      (find ((== "portnum") . name) relArgs) 
     assertR r (isBit r portnum) relPos "The portnum column must be of type bit<N>"
     assertR r (isJust $ find (\case
                                Unique _ [f1,f2] -> f1 == eVar "switch" && f2 == eVar "portnum"
                                _                -> False) relConstraints) relPos
               $ "The following constraint is required in port relation " ++ relName ++ " unique (switch,portnum)"
    
relTypeValidate :: (MonadError String me) => Refine -> Relation -> Pos -> Type -> me ()
relTypeValidate r rel p   TArray{}  = errR r p $ "Arrays are not allowed in relations (in relation " ++ name rel ++ ")"
relTypeValidate r rel p   TTuple{}  = errR r p $ "Tuples are not allowed in relations (in relation " ++ name rel ++ ")"
relTypeValidate r rel p   TOpaque{} = errR r p $ "Opaque columns are not allowed in relations (in relation " ++ name rel ++ ")"
relTypeValidate r rel p   TInt{}    = errR r p $ "Arbitrary-precision integers are not allowed in relations (in relation " ++ name rel ++ ")"
relTypeValidate _ _   _   TStruct{} = return ()
relTypeValidate _ _   _   TUser{}   = return ()
relTypeValidate _ _   _   _         = return ()

relValidate3 :: (MonadError String me) => Refine -> Relation -> me ()
relValidate3 r rel = do 
    let types = relTypes r rel
    mapM_ (\t -> relTypeValidate r rel (pos t) t) types
    maybe (return ())
          (\cyc -> errR r (pos rel) 
                     $ "Dependency cycle among types used in relation " ++ name rel ++ ":\n" ++ 
                      (intercalate "\n" $ map (show . snd) cyc))
          $ grCycle $ typeGraph r types


constraintValidate :: (MonadError String me) => Refine -> Relation -> Constraint ->  me ()
constraintValidate r rel Check{..} = exprValidate r (CtxCheck rel) constrCond

-- primary/foreign key/unique
constraintValidate r rel constr = do
    -- TODO: should all keys be different?
    mapM_ (exprValidate r (CtxRelKey rel)) $ constrFields constr
    let parent (E (EField _ p _)) = Just p
        parent _                  = Nothing
    let field  (E (EField _ _ f)) = f
        field  e                  = error $ "constraintValidate.field " ++ show e
    let guarded (E (EField _ e f)) = let TStruct _ cs = exprType' r (CtxRelKey rel) e
                                     in structFieldGuarded cs f || guarded e
        guarded _                  = False
    let oneconstr (TStruct _ [c])  = all (oneconstr . typ' r . fieldType) $ structFields [c]
        oneconstr (TStruct _ _)    = False
        oneconstr _                = True
    let (f0 : fs) = constrFields constr
    mapM_ (\f -> assertR r (parent f == parent f0) (pos f) 
                 $ "Columns in a key or unique constraint must be members of the same struct") fs
    mapM_ (\f -> assertR r (maybe True (\e -> let TStruct _ cs = exprType' r (CtxRelKey rel) e in
                                              structFieldConstructors cs (field f) == structFieldConstructors cs (field f0)) $ parent f) (pos f) 
                 $ "Columns in a key or unique constraint must belong to the same constructor") fs
    case constr of 
         ForeignKey{..} -> do frel <- checkRelation (pos constr) r CtxRefine constrForeign
                              mapM_ (exprValidate r (CtxRelForeign rel constr)) constrFArgs
                              assertR r (length constrFArgs == length constrFields) (pos constr)
                                      $ "Number of foreign fields does not match the number of local fields"
                              mapM_ (\(e1,e2) -> do let t1 = exprType r (CtxRelKey rel) e1
                                                    let t2 = exprType r (CtxRelForeign rel constr) e2
                                                    matchType (pos e1) r t1 t2) $ zip constrFields constrFArgs
                              assertR r (relCheckKey frel constrFArgs) (pos constr)
                                      $ "Foreign fields do not form a primary key"
         PrimaryKey{..} -> do mapM_ (\f -> assertR r (not $ guarded f) (pos f) 
                                                   "Primary key column only defined for some constructors") constrFields
                              mapM_ (\f -> assertR r (oneconstr $ exprType' r (CtxRelKey rel) f) (pos f) 
                                                   "Primary key must have a unique constructor") constrFields
         _              -> return () 

relCheckKey :: Relation -> [Expr] -> Bool
relCheckKey Relation{..} fs = isJust $ find check relConstraints
    where check (Unique _ _)       = False -- fs' == fs
          check (PrimaryKey _ fs') = fs' == fs
          check _                  = False

ruleValidate :: (MonadError String me) => Refine -> Relation -> Rule -> me ()
ruleValidate r rel@Relation{..} rl@Rule{..} = do
    assertR r (length ruleLHS == length relArgs) (pos rl)
            $ "Number of arguments in the left-hand-side of the rule does not match the number of fields in relation " ++ name rel
    mapM_ (exprValidate r (CtxRuleR rel rl)) ruleRHS
    mapIdxM_ (\e i -> exprValidate r (CtxRuleL rel rl i) e) ruleLHS


stateValidate :: (MonadError String me) => Refine -> Field -> me ()
stateValidate r = typeValidate r . fieldType

{-
roleValidate :: (MonadError String me) => Refine -> Role -> me ()
roleValidate r rl@Role{..} = do checkNoVar rolePos r CtxRefine roleKey
                                rel <- checkRelation rolePos r (CtxRole rl) roleTable
                                assertR r (not $ relMutable rel) rolePos 
                                        $ "Mutable relation " ++ name rel ++ " cannot be used in role declaration"
                                exprValidate r (CtxRoleGuard rl) roleCond
                                exprValidate r (CtxPktGuard rl) rolePktGuard
                                exprValidate r (CtxRole rl) roleBody
-}


portValidateFinal :: (MonadError String me) => Refine -> SwitchPort -> me ()
portValidateFinal r port@SwitchPort{..} = do
    let def = fromJust $ funcDef $ getFunc r portIn
    assert (exprIsDeterministic r def) (pos def) "Cannot synthesize non-deterministic behavior"
    mapM_ (\dp@(DirPort p dir) -> do 
             assertR r (dir == DirOut) portPos $ "Input port " ++ portName ++ " sends to another input port " ++ show dp
             assertR r (portSwitchRel r (getPort r p) == portSwitchRel r port) portPos 
                     $ "Input port " ++ portName ++ " sends to output port " ++ p ++ ", which belongs to a different switch")
          $ exprSendsToPorts r def
    maybe (return ())
          (\pout -> do let def' = fromJust $ funcDef $ getFunc r pout
                       mapM_ (\dp@(DirPort _ dir) -> do assertR r (dir == DirIn) portPos $ "Output port function " ++ name pout ++ " sends to another outputport " ++ show dp)
                             $ exprSendsToPorts r def')
        portOut
    return ()


assumeValidate :: (MonadError String me) => Refine -> Assume -> me ()
assumeValidate r a@Assume{..} = exprValidate r (CtxAssume a) assExpr

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

{-
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
-}

{-
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
-}

exprValidate :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
exprValidate r ctx e = --trace ("exprValidate " ++ show e ++ " in \n" ++ show ctx) $ 
                       do exprTraverseCtxM (exprValidate1 r) ctx e
                          exprTraverseTypeME r (exprValidate2 r) ctx e

exprTraverseTypeME :: (MonadError String me) => Refine -> (ECtx -> ExprNode Type -> me ()) -> ECtx -> Expr -> me ()
exprTraverseTypeME r = exprTraverseCtxWithM (\ctx e -> do 
    let e' = exprMap Just e
    --trace ("exprTraverseTypeME " ++ show ctx ++ "\n    " ++ show e) $ return ()
    case exprNodeType r ctx e' of
         Just t  -> do case ctxExpectType r ctx of
                            Nothing -> return ()
                            Just t' -> assertR r (matchType' r t t') (pos e) 
                                               $ "Couldn't match expected type " ++ show t' ++ " with actual type " ++ show t {-++ " (context: " ++ show ctx ++ ")"-}
                       return t
         Nothing -> error $ "Expression " ++ show e ++ " has unknown type in " ++ show ctx) 

-- This function does not perform type checking: just checks that all functions and
-- variables are defined; the number of arguments matches declarations, etc.
exprValidate1 :: (MonadError String me) => Refine -> ECtx -> ExprNode Expr -> me ()
exprValidate1 r ctx (EVar p v)          = do _ <- checkVar p r ctx v
                                             return ()
exprValidate1 r ctx (EPacket p)         = ctxCheckPkt p r ctx
exprValidate1 r ctx e@(EBuiltin p f _)  = do fun <- checkBuiltin p f
                                             (bfuncValidate fun) r ctx $ E e
exprValidate1 r ctx (EApply p f as)     = do fun <- checkFunc p r f
                                             assertR r (length as == length (funcArgs fun)) p
                                                     "Number of arguments does not match function declaration"
                                             when (not $ funcPure fun) $ do 
                                                  ctxCheckSideEffects p r ctx
                                                  -- make sure the procedure respects constraints on global variables and relations visibility
                                                  exprTraverseCtxM (exprValidate1 r) (CtxFunc fun ctx) $ fromJust $ funcDef fun
exprValidate1 _ _   (EField _ _ _)      = return ()
exprValidate1 r _   (ELocation p pr _ _)= do _ <- checkPort p r pr
                                             return ()
exprValidate1 _ _   (EBool _ _)         = return ()
exprValidate1 _ _   (EInt _ _)          = return ()
exprValidate1 _ _   (EString _ _)       = return ()
exprValidate1 _ _   (EBit _ _ _)        = return ()
exprValidate1 r _   (EStruct p c as)    = do cons <- checkConstructor p r c
                                             assertR r (length as == length (consArgs cons)) p
                                                     "Number of arguments does not match constructor declaration"
exprValidate1 _ _   (ETuple _ _)        = return ()
exprValidate1 _ _   (ESlice _ _ _ _)    = return ()
exprValidate1 _ _   (EMatch _ _ _)      = return ()
exprValidate1 r ctx (EVarDecl p v) | ctxInSetL ctx || ctxInMatchPat ctx = 
                                             checkNoVar p r ctx v
                                   | otherwise = do assertR r (ctxIsTyped ctx) p "Variable declared without a type"
                                                    assertR r (ctxIsSeq1 $ ctxParent ctx) p 
                                                            "Variable declaration is not allowed in this context"
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
exprValidate1 r ctx (EFor p v t _ _)   = do ctxCheckNotDataplane p ctx
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
exprValidate1 r ctx (EAnon p)           = assertR r (isJust $ ctxInDelete ctx) p "\"?\" only allowed in lambda-expressions"
exprValidate1 r _   (ETyped _ _ t)      = typeValidate r t
exprValidate1 r ctx (ERelPred p rel as) = do ctxCheckRelPred p r ctx
                                             rel' <- checkRelation p r ctx rel
                                             assertR r (length as == length (relArgs rel')) p
                                                     "Number of arguments does not match relation declaration"
exprValidate1 r ctx (EPut p rel _)      = do ctxCheckSideEffects p r ctx
                                             Relation{..} <- checkRelation p r ctx rel
                                             assertR r (relMutable || ctxInCLI ctx) p "Cannot modify immutable relation"
exprValidate1 r ctx (EDelete p rel _)   = do ctxCheckSideEffects p r ctx
                                             Relation{..} <- checkRelation p r ctx rel
                                             assertR r (relMutable || ctxInCLI ctx) p "Cannot modify immutable relation"

checkNoVar :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me ()
checkNoVar p r ctx v = assertR r (isNothing $ lookupVar r ctx v) p 
                                 $ "Variable " ++ v ++ " already defined in this scope"

-- Traverse again with types.  This pass ensures that all sub-expressions
-- have well-defined types that match their context
exprValidate2 :: (MonadError String me) => Refine -> ECtx -> ExprNode Type -> me ()
exprValidate2 r _   (EField p e f)      = case typ' r e of
                                               t@(TStruct _ _) -> assertR r (isJust $ find ((==f) . name) $ structArgs t) p
                                                                          $ "Unknown field \"" ++ f ++ "\" in struct of type " ++ show t 
                                               _               -> errR r (pos e) $ "Expression is not a struct"
exprValidate2 r _   (ESlice p e h l)    = case typ' r e of
                                               TBit _ w -> do assertR r (h >= l) p 
                                                                      $ "Upper bound of the slice must be greater than lower bound"
                                                              assertR r (h < w) p
                                                                      $ "Upper bound of the slice cannot exceed argument width"
                                               _        -> errR r (pos e) $ "Expression is not a bit vector"
exprValidate2 r _   (EMatch _ _ cs)     = let cs' = filter ((/= tSink) . typ' r . snd) cs 
                                              t = snd $ head cs' in
                                          mapM_ ((\e -> matchType (pos e) r t e) . snd) cs'
                                          -- TODO: pattern structure matches 
exprValidate2 r _   (ESeq _ e1 e2)      = assertR r (e1 /= tSink) (pos e2) $ "Expression appears after a sink expression"
exprValidate2 r _   (EBinOp p op e1 e2) = do case op of 
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
                                             --when (elem op [Lt, Gt, Lte, Gte, Plus, Minus, Mod] && isBit r e1) $
                                             --     assertR r ((typeWidth $ typ' r e1) <= sqlMaxIntWidth) p 
                                             --              $ "Cannot perform arithmetic operations on bit vectors wider than " ++ show sqlMaxIntWidth ++ " bits"
    where m = matchType p r e1 e2
          isint1 = assertR r (isInt r e1 || isBit r e1) (pos e1) $ "Not an integer"
          isint2 = assertR r (isInt r e2 || isBit r e2) (pos e2) $ "Not an integer"
          isbit1 = assertR r (isBit r e1) (pos e1) $ "Not a bit vector"
          isbit2 = assertR r (isBit r e2) (pos e2) $ "Not a bit vector"
          isbool = assertR r (isBool r e1) (pos e1) $ "Not a Boolean"
exprValidate2 r ctx (EVarDecl p x)      = assertR r (isJust $ ctxExpectType r ctx) p $ "Cannot determine type of variable " ++ x -- Context: " ++ show ctx
exprValidate2 r _  (EITE _ _ t e)       = let e' = maybe (tTuple []) id e
                                              cs' = filter ((/= tSink) . typ' r) [e', t] in
                                          mapM_ (\x -> matchType (pos x) r (head cs') x) cs'
exprValidate2 _ _   _                   = return ()

checkLExpr :: (MonadError String me) => Refine -> ECtx -> Expr -> me ()
checkLExpr r ctx e = assertR r (isLExpr r ctx e) (pos e) $ "Expression " ++ show e ++ " is not an l-value" -- in context " ++ show ctx


ctxCheckNotDataplane :: (MonadError String me) => Pos -> ECtx -> me ()
ctxCheckNotDataplane p ctx = do
    when (not $ ctxInCLI ctx) $ err p "loops can only be executed from command line"
    return ()

ctxCheckSideEffects :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckSideEffects p r ctx =
    case ctx of 
         CtxCLI            -> return ()
         CtxFunc f _       -> when (funcPure f) complain
         CtxBuiltin _ _ _  -> complain
         CtxApply _ _ _    -> complain
         CtxField _ _      -> complain
         CtxLocation _ _   -> complain
         CtxStruct _ _ _   -> complain
         CtxTuple _ _ _    -> complain
         CtxSlice _ _      -> complain
         CtxMatchExpr _ _  -> complain
         CtxMatchPat _ _ _ -> complain
         CtxITEIf _ _      -> complain
         CtxSetL _ _       -> complain
         CtxSend  _ _      -> complain
         CtxForkCond _ _   -> complain
         CtxWithCond _ _   -> complain
         CtxAnyCond _ _    -> complain
         CtxRelPred _ _ _  -> complain
         CtxRefine         -> complain
         _                 -> ctxCheckSideEffects p r (ctxParent ctx)
    where complain = err p $ "Side effects are not allowed in this context " ++ show ctx

ctxCheckPkt :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckPkt p r ctx =
    case ctx of 
         CtxFunc f _       -> when (funcPure f) complain
         CtxRelPred _ _ _  -> complain
         CtxRefine         -> complain
         _                 -> ctxCheckPkt p r (ctxParent ctx)
    where complain = err p $ "pkt is not available in this context" -- ++ show ctx


-- Relational predicates are allowed in the RHS of rules (at the top level) 
-- and anywhere inside assumptions
ctxCheckRelPred :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckRelPred _ _ (CtxRuleR _ _) = return ()
ctxCheckRelPred p r ctx            = ctxCheckRelPred' p r ctx

ctxCheckRelPred' :: (MonadError String me) => Pos -> Refine -> ECtx -> me ()
ctxCheckRelPred' _ _ (CtxAssume _) = return ()
ctxCheckRelPred' p r CtxRefine     = errR r p "Relational predicate is not allowed in this context"
ctxCheckRelPred' p r ctx           = ctxCheckRelPred' p r (ctxParent ctx)

structArgs :: Type -> [Field]
structArgs (TStruct _ cs) = nub $ concatMap consArgs cs
structArgs t              = error $ "structArgs " ++ show t
