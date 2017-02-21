{-# LANGUAGE FlexibleContexts #-}

module Type( WithType(..) 
           , exprType, exprType', exprTypeMaybe
           , exprTraverseTypeM
           , typ', typ''
           , isBool, isBit, isInt, isLocation, isStruct, isArray
           , matchType, matchType'
           , ctxExpectType
           {-, typeDomainSize, typeEnumerate-}) where

import Data.Maybe
import Control.Monad.Except
--import {-# SOURCE #-} Builtins

import Util
import Expr
import Syntax
import NS
import Pos
import Name
import Relation

class WithType a where
    typ  :: a -> Type

instance WithType Type where
    typ = id

instance WithType Field where
    typ = fieldType

exprTraverseTypeM :: (Monad m) => Refine -> (ECtx -> ExprNode (Maybe Type) -> m ()) -> ECtx -> Expr -> m ()
exprTraverseTypeM r = exprTraverseCtxWithM (\ctx e -> return $ exprType' r ctx e) 

exprType :: Refine -> ECtx -> Expr -> Type
exprType r ctx e = maybe (error $ "exprType: expression " ++ show e ++ " has unknown type") id $ exprTypeMaybe r ctx e

exprTypeMaybe :: Refine -> ECtx -> Expr -> Maybe Type
exprTypeMaybe r ctx e = exprFoldCtx (exprType' r) ctx e

exprType' :: Refine -> ECtx -> ExprNode (Maybe Type) -> Maybe Type
exprType' r ctx (EVar _ v)            = Just $ typ $ getVar r ctx v
exprType' _ _   (EPacket _)           = Just $ tUser packetTypeName
exprType' r _   (EApply _ f _)        = Just $ funcType $ getFunc r f
exprType' r _   (EField _ e f)        = fmap (\e' -> let TStruct _ cs = typ' r e' in
                                                     fieldType $ structGetField cs f) e
exprType' _ _   (ELocation _ _ _)     = Just tLocation
exprType' _ _   (EBool _ _)           = Just tBool
exprType' r ctx (EInt _ _)            = case ctxExpectType r ctx of
                                             t@(Just (TBit _ _)) -> t
                                             _                   -> Just tInt
exprType' _ _   (EString _ _)         = Just tString
exprType' _ _   (EBit _ w _)          = Just $ tBit w
exprType' r _   (EStruct _ c _)       = Just $ tUser $ name $ consType r c
exprType' _ _   (ETuple _ fs)         = fmap tTuple $ sequence fs
exprType' _ _   (ESlice _ _ h l)      = Just $ tBit $ h - l + 1
exprType' _ _   (EMatch _ _ cs)       = snd $ head cs
exprType' r ctx (EVarDecl _ _)        = ctxExpectType r ctx
exprType' _ _   (ESeq _ _ e2)         = e2
exprType' _ _   (EPar _ _ _)          = Just tSink
exprType' _ _   (EITE _ _ t _)        = t
exprType' _ _   (EDrop _)             = Just tSink
exprType' _ _   (ESet _ _ _)          = Just $ tTuple []
exprType' _ _   (ESend  _ _)          = Just tSink
exprType' r _   (EBinOp _ op (Just e1) (Just e2)) = 
                                  case op of
                                       Eq     -> Just tBool
                                       Neq    -> Just tBool
                                       Lt     -> Just tBool
                                       Gt     -> Just tBool
                                       Lte    -> Just tBool
                                       Gte    -> Just tBool
                                       And    -> Just tBool
                                       Or     -> Just tBool
                                       Impl   -> Just tBool
                                       Plus   -> Just $ if' (isBit r t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                       Minus  -> Just $ if' (isBit r t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                       ShiftR -> Just t1
                                       ShiftL -> Just t1
                                       Mod    -> Just t1
                                       Concat -> Just $ tBit (typeWidth t1 + typeWidth t2)
    where t1 = typ' r e1
          t2 = typ' r e2
exprType' _ _   (EBinOp _ ShiftR e1 _) = e1
exprType' _ _   (EBinOp _ ShiftL e1 _) = e1
exprType' _ _   (EBinOp _ _ _ _)       = Nothing
exprType' _ _   (EUnOp _ Not _)        = Just tBool
exprType' _ _   (EFork _ _ _ _ _)      = Just tSink
exprType' _ _   (EWith _ _ _ _ b _)    = b
exprType' _ _   (EAny  _ _ _ _ b _)    = b
exprType' r ctx (EPHolder _)           = ctxExpectType r ctx
exprType' _ _   (ETyped _ _ t)         = Just t
exprType' _ _   (ERelPred _ _ _)       = Just tBool


-- Unwrap typedef's down to actual type definition
typ' :: (WithType a) => Refine -> a -> Type
typ' r x = case typ x of
                TUser _ n   -> typ' r $ fromJust $ tdefType $ getType r n
                t           -> t

-- Similar to typ', but does not unwrap the last typedef if it is a struct
typ'' :: (WithType a) => Refine -> a -> Type
typ'' r x = case typ x of
                 t'@(TUser _ n) -> case fromJust $ tdefType $ getType r n of
                                        TStruct _ _ -> t'
                                        t           -> typ'' r t
                 t         -> t

isBool :: (WithType a) => Refine -> a -> Bool
isBool r a = case typ' r a of
                  TBool _ -> True
                  _       -> False

isBit :: (WithType a) => Refine -> a -> Bool
isBit r a = case typ' r a of
                 TBit _ _ -> True
                 _        -> False

isInt :: (WithType a) => Refine -> a -> Bool
isInt r a = case typ' r a of
                 TInt _ -> True
                 _      -> False

isLocation :: (WithType a) => Refine -> a -> Bool
isLocation r a = case typ' r a of
                      TLocation _ -> True
                      _           -> False

isStruct :: (WithType a) => Refine -> a -> Bool
isStruct r a = case typ' r a of
                    TStruct _ _ -> True
                    _           -> False

isArray :: (WithType a) => Refine -> a -> Bool
isArray r a = case typ' r a of
                   TArray _ _ _ -> True
                   _            -> False

matchType :: (MonadError String me, WithType a, WithPos a, WithType b) => Refine -> a -> b -> me ()
matchType r x y = assertR r (matchType' r x y) (pos x) $ "Incompatible types " ++ show (typ x) ++ " and " ++ show (typ y)


matchType' :: (WithType a, WithType b) => Refine -> a -> b -> Bool
matchType' r x y = 
    case (t1, t2) of
         (TLocation _   , TLocation _)    -> True
         (TBool _       , TBool _)        -> True
         (TBit _ w1     , TBit _ w2)      -> w1==w2
         (TInt _        , TInt _)         -> True
         (TString _     , TString _)      -> True
         (TSink _       , TSink _)        -> True
         (TArray _ a1 l1, TArray _ a2 l2) -> matchType' r a1 a2 && l1 == l2
         (TStruct _ cs1 , TStruct _ cs2)  -> (length cs1 == length cs2) &&
                                             (all (\(c1, c2) -> consName c1 == consName c2) $ zip cs1 cs2)
         _                                -> False
    where t1 = typ' r x
          t2 = typ' r y

{-
typeDomainSize :: Refine -> Type -> Integer
typeDomainSize r t = 
    case typ' r undefined t of
         TBool _       -> 2
         TUInt _ w     -> 2^w
         TStruct _ fs  -> product $ map (typeDomainSize r . fieldType) fs
         TArray _ t' l -> fromIntegral l * typeDomainSize r t'
         TUser _ _     -> error "Type.typeDomainSize TUser"
         TLocation _   -> error "Not implemented: Type.typeDomainSize TLocation"

typeEnumerate :: Refine -> Type -> [Expr]
typeEnumerate r t = 
    case typ' r undefined t of
         TBool _      -> [EBool nopos False, EBool nopos True]
         TUInt _ w    -> map (EInt nopos w) [0..2^w-1]
         TStruct _ fs -> map (EStruct nopos sname) $ fieldsEnum fs
         TArray _ _ _ -> error "Not implemented: Type.typeEnumerate TArray"
         TUser _ _    -> error "Type.typeEnumerate TUser"
         TLocation _  -> error "Not implemented: Type.typeEnumerate TLocation"
    where TUser _ sname = typ'' r undefined t
          fieldsEnum []     = [[]]
          fieldsEnum (f:fs) = concatMap (\vs -> map (:vs) $ typeEnumerate r $ fieldType f) $ fieldsEnum fs
-}

-- Infer expected type from context
ctxExpectType :: Refine -> ECtx -> Maybe Type
ctxExpectType _ (CtxRoleGuard _)                   = Just tBool
ctxExpectType _ (CtxRole _)                        = Just tSink
ctxExpectType _ (CtxFunc f)                        = Just $ funcType f
ctxExpectType _ (CtxAssume _)                      = Just tBool
ctxExpectType _ (CtxRelation _)                    = Nothing
ctxExpectType _ (CtxRuleL rel _ i)                 = let args = relArgs rel in
                                                     if' (i < length args) (Just $ fieldType $ args !! i) Nothing
ctxExpectType _ (CtxRuleR _ _)                     = Just tBool
ctxExpectType r (CtxApply (EApply _ f _) _ i)      = let args = funcArgs $ getFunc r f in
                                                     if' (i < length args) (Just $ fieldType $ args !! i) Nothing
ctxExpectType _ (CtxField (EField _ _ _) _)        = Nothing
ctxExpectType r (CtxLocation (ELocation _ rl _) _) = Just $ relRecordType $ getRelation r $ roleTable $ getRole r rl
ctxExpectType r (CtxStruct (EStruct _ c _) _ i)    = let args = consArgs $ getConstructor r c in
                                                     if' (i < length args) (Just $ typ $ args !! i) Nothing
ctxExpectType r (CtxTuple _ ctx i)                 = case ctxExpectType r ctx of 
                                                          Just t -> let TTuple _ fs = typ' r t in 
                                                                    if' (i < length fs) (Just $ fs !! i) Nothing
                                                          Nothing -> Nothing
ctxExpectType _ (CtxSlice _ _)                     = Nothing
ctxExpectType _ (CtxMatchExpr _ _)                 = Nothing
ctxExpectType r (CtxMatchPat e ctx _)              = ctxExpectType r (CtxMatchExpr e ctx)
ctxExpectType r (CtxMatchVal _ ctx _)              = ctxExpectType r ctx
ctxExpectType _ (CtxSeq1 _ _)                      = Nothing
ctxExpectType r (CtxSeq2 _ ctx)                    = ctxExpectType r ctx
ctxExpectType _ (CtxPar1 _ _)                      = Just tSink
ctxExpectType _ (CtxPar2 _ _)                      = Just tSink
ctxExpectType _ (CtxITEIf _ _)                     = Just tBool
ctxExpectType r (CtxITEThen _ ctx)                 = ctxExpectType r ctx
ctxExpectType r (CtxITEElse _ ctx)                 = ctxExpectType r ctx
ctxExpectType r (CtxSetL e@(ESet _ _ rhs) ctx)     = exprTypeMaybe r (CtxSetR e ctx) rhs
ctxExpectType r (CtxSetR (ESet _ lhs _) ctx)       = exprTypeMaybe r ctx lhs -- avoid infinite recursion by evaluating lhs standalone
ctxExpectType _ (CtxSend _ _)                      = Just $ tLocation
ctxExpectType r (CtxBinOpL e ctx)                  = case exprBOp e of
                                                          Eq     -> trhs
                                                          Neq    -> trhs
                                                          Lt     -> trhs
                                                          Gt     -> trhs
                                                          Lte    -> trhs
                                                          Gte    -> trhs
                                                          And    -> Just tBool
                                                          Or     -> Just tBool
                                                          Impl   -> Just tBool
                                                          Plus   -> trhs
                                                          Minus  -> trhs
                                                          ShiftR -> Nothing
                                                          ShiftL -> Nothing
                                                          Mod    -> Nothing
                                                          Concat -> Nothing
    where trhs = exprTypeMaybe r ctx $ exprRight e
ctxExpectType r (CtxBinOpR e ctx)                  = case exprBOp e of
                                                          Eq     -> tlhs
                                                          Neq    -> tlhs
                                                          Lt     -> tlhs
                                                          Gt     -> tlhs
                                                          Lte    -> tlhs
                                                          Gte    -> tlhs
                                                          And    -> Just tBool
                                                          Or     -> Just tBool
                                                          Impl   -> Just tBool
                                                          Plus   -> tlhs
                                                          Minus  -> tlhs
                                                          ShiftR -> Nothing
                                                          ShiftL -> Nothing
                                                          Mod    -> Nothing
                                                          Concat -> Nothing
    where tlhs = exprTypeMaybe r ctx $ exprLeft e
ctxExpectType _ (CtxUnOp (EUnOp _ Not _) _)        = Just tBool
ctxExpectType _ (CtxForkCond _ _)                  = Just tBool
ctxExpectType _ (CtxForkBody _ _)                  = Just tSink
ctxExpectType _ (CtxWithCond _ _)                  = Just tBool
ctxExpectType r (CtxWithBody _ ctx)                = ctxExpectType r ctx
ctxExpectType r (CtxWithDef _ ctx)                 = ctxExpectType r ctx
ctxExpectType _ (CtxAnyCond _ _)                   = Just tBool
ctxExpectType r (CtxAnyBody _ ctx)                 = ctxExpectType r ctx
ctxExpectType r (CtxAnyDef _ ctx)                  = ctxExpectType r ctx
ctxExpectType _ (CtxTyped (ETyped _ _ t) _)        = Just t
ctxExpectType r (CtxRelPred e _ i)                 = let args = relArgs $ getRelation r $ exprRel e in
                                                     if' (i < length args) (Just $ fieldType $ args !! i) Nothing
ctxExpectType _ ctx                                = error $ "ctxExpectType " ++ show ctx
