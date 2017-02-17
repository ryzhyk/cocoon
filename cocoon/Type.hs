{-# LANGUAGE FlexibleContexts #-}

module Type( WithType(..) 
           , exprType
           , typ', typ''
           , isBool, isBit, isLocation, isStruct, isArray
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

exprType :: Refine -> ECtx -> Expr -> Type
exprType r ctx e = exprFoldCtx (etype r) ctx e

etype :: Refine -> ECtx -> ExprNode Type -> Type
etype r ctx (EVar _ v)          = typ $ getVar r ctx v
etype _ _   (EPacket _)         = tUser packetTypeName
etype r _   (EApply _ f _)      = funcType $ getFunc r f
etype r _   (EField _ e f)      = let TStruct _ cs = typ' r e in
                                  fieldType $ structGetField cs f
etype _ _   (ELocation _ _ _)   = tLocation
etype _ _   (EBool _ _)         = tBool
etype _ _   (EInt _ _)          = tInt
etype _ _   (EString _ _)       = tString
etype _ _   (EBit _ w _)        = tBit w
etype r _   (EStruct _ c _)     = tUser $ name $ consType r c
etype _ _   (ETuple _ fs)       = tTuple fs
etype _ _   (ESlice _ _ h l)    = tBit $ h - l + 1
etype _ _   (EMatch _ _ cs)     = fst $ head cs
etype r ctx (EVarDecl p v)      = maybe (error $ "exprType: cannot infer type of variable " ++ v ++ "(" ++ show p ++ ")") id 
                                  $ ctxExpectType r ctx
etype _ _   (ESeq _ _ e2)       = e2
etype _ _   (EPar _ _ _)        = tSink
etype _ _   (EITE _ _ t _)      = t
etype _ _   (EDrop _)           = tSink
etype _ _   (ESet _ _ _)        = tTuple []
etype _ _   (ESend  _ _)        = tSink
etype r _   (EBinOp _ op e1 e2) = case op of
                                       Eq     -> tBool
                                       Neq    -> tBool
                                       Lt     -> tBool
                                       Gt     -> tBool
                                       Lte    -> tBool
                                       Gte    -> tBool
                                       And    -> tBool
                                       Or     -> tBool
                                       Impl   -> tBool
                                       Plus   -> if' (isBit r t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                       Minus  -> if' (isBit r t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                       ShiftR -> t1
                                       ShiftL -> t1
                                       Mod    -> t1
                                       Concat -> tBit (typeWidth t1 + typeWidth t2)
    where t1 = typ' r e1
          t2 = typ' r e2
etype _ _   (EUnOp _ Not _)      = tBool
etype _ _   (EFork _ _ _ _ _)    = tSink
etype _ _   (EWith _ _ _ _ b _)  = b
etype _ _   (EAny  _ _ _ _ b _)  = b
etype r ctx (EPHolder p)         = maybe (error $ "exprType: cannot infer type of placeholder from context (" ++ show p ++ ")") id
                                   $ ctxExpectType r ctx
etype _ _   (ETyped _ _ t)       = t


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
ctxExpectType _ (CtxRole _)                        = Just tSink
ctxExpectType _ (CtxFunc f)                        = Just $ funcType f
ctxExpectType _ (CtxAssume _)                      = Just tBool
ctxExpectType _ (CtxRelation _)                    = Nothing
ctxExpectType _ (CtxRule _)                        = Nothing
ctxExpectType r (CtxApply (EApply _ f _) _ i)      = Just $ fieldType $ (funcArgs $ getFunc r f) !! i
ctxExpectType _ (CtxField (EField _ _ _) _)        = Nothing
ctxExpectType r (CtxLocation (ELocation _ rl _) _) = Just $ relRecordType $ getRelation r $ roleTable $ getRole r rl
ctxExpectType r (CtxStruct (EStruct _ c _) _ i)    = Just $ typ $ (consArgs $ getConstructor r c) !! i
ctxExpectType r (CtxTuple _ ctx i)                 = fmap (\t -> let TTuple _ fs = typ' r t in fs !! i) $ ctxExpectType r ctx
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
ctxExpectType r (CtxSetL e@(ESet _ _ rhs) ctx)     = Just $ exprType r (CtxSetR e ctx) rhs
ctxExpectType _ (CtxSetR _ _)                      = Nothing
ctxExpectType _ (CtxSend _ _)                      = Just $ tLocation
ctxExpectType _ (CtxBinOpL _ _)                    = Nothing
ctxExpectType _ (CtxBinOpR _ _)                    = Nothing
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
ctxExpectType _ ctx                                = error $ "ctxExpectType " ++ show ctx
