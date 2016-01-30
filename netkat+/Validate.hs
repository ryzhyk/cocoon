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

-- Validate spec.  Constructs a series of contexts, sequentially applying 
-- refinements from the spec, and validates each context separately.
validate :: (MonadError String me) => Spec -> me ()
validate (Spec (r:rs)) = do
    final <- foldM (\prev new -> do {validate1 prev; combine prev new}) r rs
    validate1 final

-- Apply definitions in new on top of prev.
combine :: (MonadError String me) => Refine -> Refine -> me Refine
combine prev new = do 
    prev' <- foldM (\r role -> do assert (isJust $ find ((==role) . roleName) (refineRoles r)) (pos new) 
                                         $ "Role " ++ role ++ " is undefined in this context"
                                  return r{refineRoles = filter ((/=role) . roleName) $ refineRoles r}) prev (refineTarget new)
    let types = refineTypes prev'     ++ refineTypes new
        funcs = refineFuncs prev'     ++ refineFuncs new
        roles = refineRoles prev'     ++ refineRoles new
        rlocs = refineLocations prev' ++ refineLocations new 
    return $ Refine nopos [] types funcs roles rlocs


-- construct dependency graph
typeGraph :: Refine -> G.Gr TypeDef ()
typeGraph r = undefined

-- Validate refinement with previous definitions inlined
validate1 :: (MonadError String me) => Refine -> me ()
validate1 r@Refine{..} = do
    uniqNames (\n -> "Multiple definitions of type " ++ n) refineTypes
    assert (isJust $ find ((==packetTypeName) . tdefName) refineTypes) (pos r) $ packetTypeName ++ " is undefined"
    uniqNames (\n -> "Multiple definitions of function " ++ n) refineFuncs
    uniq locRole (\r -> "Multiple container definitions for role " ++ locRole r) refineLocations
    mapM_ (typeValidate r . tdefType) refineTypes
    -- TODO: check for cycles in the types graph - catch recursive type definitions
    case grCycle (typeGraph r) of
         Nothing -> return ()
         Just t  -> err (pos $ snd $ head t) $ "Recursive type definition: " ++ (intercalate "->" $ map (name . snd) t)

    mapM_ (funcValidate r) refineFuncs
    mapM_ (roleValidate r) refineRoles
    mapM_ (rlocValidate r) refineLocations
    -- TODO: check for cycles in the locations graph

typeValidate :: (MonadError String me) => Refine -> Type -> me ()
typeValidate _ (TUInt p w)    = assert (w>0) p "Integer width must be greater than 0"
typeValidate r (TStruct _ fs) = do uniqNames (\f -> "Multiple definitions of field " ++ f) fs
                                   mapM_ (typeValidate r . fieldType) fs
typeValidate r (TUser   p n)  = do checkType p r n
                                   return ()
typeValidate _ _              = return ()

funcValidate :: (MonadError String me) => Refine -> Function -> me ()
funcValidate r Function{..} = do
    uniqNames (\a -> "Multiple definitions of argument " ++ a) funcArgs
    mapM_ (typeValidate r . fieldType) funcArgs
    typeValidate r funcType

roleValidate :: (MonadError String me) => Refine -> Role -> me ()
roleValidate r role@Role{..} = do
    uniqNames (\k -> "Multiple definitions of key " ++ k) roleKeys
    mapM_ (typeValidate r . fieldType) roleKeys
    exprValidate r role roleKeyRange
    statValidate r role roleBody
    return ()

rlocValidate :: (MonadError String me) => Refine -> RoleLocation -> me ()
rlocValidate r rloc@RoleLocation{..} = do
    role <- checkRole (pos rloc) r locRole
    exprValidate r role locExpr
    assert (isLocation r role locExpr) (pos locExpr) "Not a valid location"
    return ()

exprValidate :: (MonadError String me) => Refine -> Role -> Expr -> me ()
exprValidate r role (EKey p k) = do 
   checkKey p role k
   return ()
exprValidate r role (EApply p f as) = do
    func <- checkFunc p r f
    assert ((length $ funcArgs func) == length as) p "Number of arguments does not match function declaration"
    mapM_ (\(formal,actual) -> do exprValidate r role actual
                                  matchType r role formal actual) 
          $ zip (funcArgs func) as
exprValidate r role (EField p s f) = do
    exprValidate r role s
    case typ' r role s of
         TStruct _ fs -> assert (isJust $ find ((==f) . fieldName) fs) p $ "Unknown field " ++ f
         _            -> err p $ "Expression is not of struct type"

exprValidate r role (ELocation p rname as) = do
    role' <- checkRole p r rname
    assert ((length $ roleKeys role') == length as) p "Number of keys does not match role declaration"
    mapM_ (\(formal,actual) -> do exprValidate r role' actual
                                  matchType r role' formal actual) 
          $ zip (roleKeys role') as

exprValidate r role (EStruct p n as) = do
    t <- checkType p r n
    case typ' r role (tdefType t) of
         TStruct _ fs -> do assert (length as == length fs) p "Number of fields does not match struct definition"
                            mapM_ (\(field, e) -> do exprValidate r role e
                                                     matchType r role field e)
                                  $ zip fs as
         _            -> err p $ n ++ " is not a struct type"
exprValidate r role (EBinOp p op left right) = do
    exprValidate r role left
    exprValidate r role right
    case op of
         Eq   -> matchType r role left right
         And  -> do assert (isBool r role left)  (pos left)  $ "Not a boolean expression"
                    assert (isBool r role right) (pos right) $ "Not a boolean expression"
         Or   -> do assert (isBool r role left)  (pos left)  $ "Not a boolean expression"
                    assert (isBool r role right) (pos right) $ "Not a boolean expression"
         Plus -> do assert (isUInt r role left)  (pos left)  $ "Not an integer expression"
                    assert (isUInt r role right) (pos right) $ "Not an integer expression"
                    matchType r role left right
         Mod  -> do assert (isUInt r role left)  (pos left)  $ "Not an integer expression"
                    assert (isUInt r role right) (pos right) $ "Not an integer expression"
exprValidate r role (EUnOp p op e) = do
    exprValidate r role e
    case op of
         Not -> assert (isBool r role e) (pos e)  $ "Not a boolean expression"

exprValidate r role (ECond p cs def) = do
    exprValidate r role def
    mapM_ (\(cond, e)-> do exprValidate r role cond
                           exprValidate r role e
                           assert (isBool r role cond) (pos cond) $ "Not a boolean expression"
                           matchType r role e def) cs

exprValidate _ _ _ = return ()


lexprValidate :: (MonadError String me) => Refine -> Role -> Expr -> me ()
lexprValidate r role e = do
    exprValidate r role e
    assert (isLExpr e) (pos e) "Not an l-value"

isLExpr :: Expr -> Bool
isLExpr (EKey _ _)        = False
isLExpr (EPacket _)       = True
isLExpr (EApply _ _ _)    = False
isLExpr (EField _ s _)    = isLExpr s
isLExpr (ELocation _ _ _) = False
isLExpr (EBool _ _)       = False
isLExpr (EInt _ _)        = False
isLExpr (EStruct _ _ _)   = False
isLExpr (EBinOp _ _ _ _)  = False
isLExpr (EUnOp _ _ _)     = False
isLExpr (ECond _ _ _)     = False

statValidate :: (MonadError String me) => Refine -> Role -> Statement -> me Bool
statValidate r role (SSeq p h t) = do
    sends <- statValidate r role h
    assert (not sends) (pos h) "Send not allowed in the middle of a sequence"
    statValidate r role t

statValidate r role (SPar p h t) = do
    sends1 <- statValidate r role h
    sends2 <- statValidate r role t
    return $ sends1 || sends2

statValidate r role (STest p c) = do
    exprValidate r role c
    assert (isBool r role c) (pos c) "Filter must be a boolean expression"
    return False

statValidate r role (SSet p lval rval) = do
    exprValidate r role rval
    lexprValidate r role lval
    matchType r role lval rval
    return False

statValidate r role (SSend p dst) = do
    exprValidate r role dst
    assert (isLocation r role dst) (pos dst) "Not a valid location"
    return True
