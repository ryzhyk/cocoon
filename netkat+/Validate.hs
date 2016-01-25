module Validate () where

import Control.Monad.Error

import Syntax

-- Validate spec.  Constructs a series of contexts, sequentially applying 
-- refinements from the spec, and validates each context separately.
validate :: (MonadError String me) => Spec -> me ()
validate (Spec r:rs) = 
    final <- foldM (\prev new -> do {validate1 prev; combine prev new}) r rs
    validate1 final

-- Apply definitions in new on top of prev.
combine :: (MonadError String me) => Refine -> Refine -> me Refine
combine prev new = do 
    prev' <- foldM (\r role -> do assert (isJust $ find ((==role) . roleName) (refineRoles r)) (pos new) 
                                         "Role " ++ role ++ " is undefined in this context"
                                  return r{refineRoles = filter ((==role) . roleName) r }) prev (refineTarget new)
    types = refineTypes prev' ++ refineTypes new
    funcs = refineFuncs prev' ++ refineFuncs new
    roles = refineRoles prev' ++ refineRoles new 
    return $ Refine nopos [] types funcs roles


-- construct dependency graph
typeGraph :: Refine -> G.Graph TypeDef
typeGraph r = undefined

-- Validate refinement with previous definitions inlined
validate1 :: (MonadError String me) => Refine -> me Refine
validate1 r@Refine{..} = do
    uniqNames (\n -> "Multiple definitions of type " ++ n)     refineTypes
    uniqNames (\n -> "Multiple definitions of function " ++ n) refineFuncs
    uniqNames (\n -> "Multiple definitions of role " ++ n)     refineRoles
    mapM_ (typeValidate r . tdefType) refineTypes
    -- check for cycles in the types graph - catch recursive type definitions
    case grCycle (typeGraph refineTypes) of
         Nothing -> return ()
         Just t  -> err (pos $ snd $ head t) $ "Recursive type definition: " ++ (intercalate "->" $ map tdefName t)

    mapM_ (funcValidate r) refineFuncs
    mapM_ (roleValidate r) refineRoles

typeValidate :: (MonadError String me) => Refine -> Type -> me ()
typeValidate _ (TUInt _ w)    = assert (w>0) (pos t) "Integer width must be greater than 0"
typeValidate r (TStruct _ fs) = do uniqNames (\f -> "Multiple definitions of field " ++ f) fs
                                   mapM (typeValidate r . snd) fs
typeValidate r (TUser   _ n)  = do _ <- checkType r n
typeValidate _ _              = return ()

funcValidate :: (MonadError String me) => Refine -> Function -> me ()
funcValidate r Function{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) funcArgs
    mapM_ (typeValidate r . fieldType) funcArgs
    typeValidate r funcType

roleValidate :: (MonadError String me) => Refine -> Role -> me ()
roleValidate r role@Role{..} = do
    uniqNames (\k -> "Multiple definitions of key " ++ k) roleKeys
    mapM_ (typeValidate r . fieldType) roleKey
    exprValidate r role roleKeyRange
    mapM_ (exprValidate r role) roleContains
    statValidate r role roleBody

exprValidate :: (MonadError String me) => Refine -> Role -> Expr -> me ()
exprValidate r role (EVar _ v) = do 
   checkVar v
exprValidate r role (EApply p f as) = do
    func <- checkFunc r f
    assert ((length $ funcArgs func) == length as) p "Number of arguments does not match function declaration"
    mapM_ (\(formal,actual) -> do exprValidate r role actual
                                  matchType formal actual) 
          $ zip (funcArgs func) as
exprValidate r role (EField p s f) = do
    exprValidate r role s
    case typ' s of
         TStruct _ fs -> assert (isJust $ find ((==f) . fieldName) fs) p $ "Unknown field " ++ f
         _            -> err p $ "Expression " ++ show s ++ " is not of struct type"

exprValidate r role (ELocation p rname as) = do
    role' <- checkRole r rname
    assert ((length $ roleKeys role') == length as) p "Number of keys does not match role declaration"
    mapM_ (\(formal,actual) -> do exprValidate r role actual
                                  matchType formal actual) 
          $ zip (roleKeys role's) as

exprValidate r role (EStruct p n as) = do
    t <- checkType r n
    case typ' t of
         TStruct _ fs -> do assert (length as == length fs) p "Number of fields does not match struct definition"
                            mapM_ (\field e -> do exprValidate r role e
                                                  matchType field e)
                                  $ zip fs as
         _            -> err p $ n ++ " is not a struct type"
exprValidate r role (EBinOp p op left right) = do
    exprValidate r role left
    exprValidate r role right
    case op of
         Eq   -> matchType left right
         And  -> do assert (isBool left)  (pos left)  $ "Not a boolean expression"
                    assert (isBool right) (pos right) $ "Not a boolean expression"
         Or   -> do assert (isBool left)  (pos left)  $ "Not a boolean expression"
                    assert (isBool right) (pos right) $ "Not a boolean expression"
         Plus -> do assert (isUInt left)  (pos left)  $ "Not an integer expression"
                    assert (isUInt right) (pos right) $ "Not an integer expression"
                    matchType left right
         Mod  -> do assert (isUInt left)  (pos left)  $ "Not an integer expression"
                    assert (isUInt right) (pos right) $ "Not an integer expression"
exprValidate r role (EUnOp p op e) = do
    exprValidate r role e
    case op of
         Not -> assert (isBool e) (pos e)  $ "Not a boolean expression"

exprValidate r role (ECond p cs def) = do
    exprValidate def
    mapM_ (\(cond, e)-> do exprValidate r role cond
                           exprValidate r role e
                           assert (isBool cond) (pos cond) $ "Not a boolean expression"
                           matchType e def) cs

exprValidate _ _ _ = return ()
