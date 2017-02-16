{-# LANGUAGE FlexibleContexts #-}

module Type( WithType(..) 
           , typ', typ''
           , isBool, isBit, isLocation, isStruct, isArray
           , matchType, matchType'
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
etype r ctx (EVar _ v)          = fieldType $ ctxGetVar r ctx v
etype _ _   (EPacket _)         = tUser packetTypeName
etype r _   (EApply _ f _)      = funcType $ getFunc r f
etype r ctx (EField _ e f)      = let TStruct _ cs = typ' r e in
                                  fieldType $ structGetField cs f
etype _ _   (ELocation _ r as)  = tLocation
etype _ _   (EBool _ _)         = tBool
etype _ _   (EInt _ _)          = tInt
etype _ _   (EString _ _)       = tString
etype _ _   (EBit _ w _)        = tBit w
etype r _   (EStruct _ c _)     = tUser $ name $ consType r c
etype _ _   (ETuple _ fs)       = tTuple fs
etype _ _   (ESlice _ _ h l)    = tBit $ h - l + 1
etype _ _   (EMatch _ _ cs)     = fst $ head cs
etype r ctx (EVarDecl _ _)      = ctxExpectType r ctx
etype _ _   (ESeq _ _ e2)       = e2
etype _ _   (EPar _ e1 e2)      = tSink
etype _ _   (EITE _ _ t _)      = etype t
etype _ _   (EDrop _)           = tSink
etype _ _   (ESet _ _ _)        = tTuple []
etype _ _   (ESend  _ e)        = tSink
etype _ ctx (EBinOp _ op e1 e2) = case op of
                                     Eq     -> tBool
                                     Neq    -> tBool
                                     Lt     -> tBool
                                     Gt     -> tBool
                                     Lte    -> tBool
                                     Gte    -> tBool
                                     And    -> tBool
                                     Or     -> tBool
                                     Impl   -> tBool
                                     Plus   -> if' (isBit t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                     Minus  -> if' (isBit t1) (tBit (max (typeWidth t1) (typeWidth t2))) tInt
                                     ShiftR -> t1
                                     ShiftL -> t1
                                     Mod    -> t1
                                     Concat -> tBit (typeWidth t1 + typeWidth t2)
    where t1 = typ' ctx e1
          t2 = typ' ctx e2
etype _ _   (EUnOp _ Not e)      = tBool
etype _ _   (EFork _ _ _ _ _)    = tSink
etype _ _   (EWith _ _ _ _ b _)  = b
etype _ _   (EAny  _ _ _ _ b _)  = b
etype r ctx (EPHolder _)         = ctxExpectType r ctx
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

ctxGetVar :: Refine -> ECtx -> String -> Field
ctxGetVar = error "ctxGetVar is undefined"

ctxExpectType :: Refine -> ECtx -> Maybe Type
ctxExpectType _ (CtxRole role)                        = Just tSink
ctxExpectType _ (CtxFunc f)                           = Just $ funcType f
ctxExpectType _ (CtxAssume _)                         = Just tBool
ctxExpectType _ (CtxRelation _)                       = Nothing
ctxExpectType _ (CtxRule _)                           = Nothing
ctxExpectType r (CtxApply (EApply _ f _) _ i)         = Just $ fieldType $ (funcArgs $ getFunc r f) !! i
ctxExpectType _ (CtxField (EField _ _ _) _)           = Nothing
ctxExpectType r (CtxLocation (ELocation _ rl k) _)    = Just $ relRecordType $ getRelation r $ roleTable $ getRole r rl
ctxExpectType r (CtxStruct (EStruct _ c _) _ i)       = Just $ typ $ (consArgs $ getConstructor r c) !! i
ctxExpectType r (CtxTuple _ ctx i)                    = fmap (\t -> let TTuple _ fs = typ' r t in fs !! i) $ ctxExpectType r ctx
ctxExpectType r (CtxSlice _ _)                        = Nothing
{-
ctxExpectType r (CtxMatchExpr {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxMatchPat  {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
ctxExpectType r (CtxMatchVal  {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
ctxExpectType r (CtxSeq1      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxSeq2      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxPar1      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxPar2      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxITEIf     {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxITEThen   {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxITEElse   {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxSetL      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxSetR      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxSend      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxBinOpL    {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxBinOpR    {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxUnOp      {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxForkCond  {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxForkBody  {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxWithCond  {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxWithBody  {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxWithDef   {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxAnyCond   {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxAnyBody   {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxAnyDef    {ctxParExpr::ENode, ctxPar::ECtx}
ctxExpectType r (CtxTyped     {ctxParExpr::ENode, ctxPar::ECtx}-}
