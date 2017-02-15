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
{-# LANGUAGE FlexibleContexts #-}

module Type( WithType(..) 
           , typ', typ''
           , isBool, isBit, isLocation, isStruct, isArray
           , matchType, matchType'
           {-, typeDomainSize, typeEnumerate-}) where

import Data.Maybe
import Control.Monad.Except
--import {-# SOURCE #-} Builtins

import Syntax
import NS
import Pos

class WithType a where
    typ  :: Refine -> ECtx -> a -> Type

instance WithType Type where
    typ _ _ t = t

instance WithType Field where
    typ _ _ = fieldType


instance WithType Expr where
    typ _ ctx   (EVar _ v)          = fieldType $ getVar ctx v
    typ _ _     (EPacket _)         = tUser packetTypeName
    typ r ctx   (EApply _ f as)     = funcType $ getFunc r f
    typ r ctx   (EField _ e f)      = let TStruct _ cs = typ' r ctx e in
                                      fieldType $ structGetField cs f
    typ _ _     (ELocation _ r as)  = tLocation
    typ _ _     (EBool _ _)         = tBool
    typ _ _     (EInt _ _)          = tInt
    typ _ _     (EString _ _)       = tString
    typ _ _     (EBit _ w _)        = tBit w
    typ r _     (EStruct _ c _)     = tUser $ consType r c
    typ r ctx e@(ETuple _ fs)       = tTuple $ mapIdx (\f i -> typ r (CtxTuple ctx e i) f) fs
    typ _ _     (ESlice _ _ h l)    = tBit $ h - l + 1
    typ r ctx e@(EMatch _ m cs)     = (\(pat, v) -> typ r (CtxMatchCase ctx m pat) v) $ head cs
    typ r ctx   (EVarDecl _ v)      = ctxExpectType r ctx
    typ r ctx e@(ESeq _ e1 e2)      = typ r (CtxSeqAfter ctx e1) e2
    typ _ _     (EPar _ e1 e2)      = tSink
    typ r ctx   (EITE _ c t me)     = typ r ctx t
    typ _ _     (EDrop _)           = tSink
    typ _ _     (ESet _ _ _)        = tTuple []
    typ _ _     (ESend  _ e)        = tSink
    typ r ctx   (EBinOp _ op e1 e2) = case op of
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
        where t1 = typ' r ctx e1
              t2 = typ' r ctx e2
    typ _ _     (EUnOp _ Not e)      = tBool
    typ _ _     (EFork _ _ _ _ _)    = tSink
    typ _ ctx e@(EWith _ _ _ _ b _)  = typ r (CtxWith ctx e) b
    typ _ ctx e@(EAny  _ _ _ _ b _)  = typ r (CtxWith ctx e) b
    typ r ctx   (EPHolder _)         = ctxExpectType r ctx
    typ _ _     (ETyped _ _ t)       = t



-- Unwrap typedef's down to actual type definition
typ' :: (WithType a) => Refine -> ECtx -> a -> Type
typ' r ctx x = case typ r ctx x of
                    TUser _ n   -> typ' r ctx $ fromJust $ tdefType $ getType r n
                    t           -> t


-- Similar to typ', but does not unwrap the last typedef if it is a struct
typ'' :: (WithType a) => Refine -> ECtx -> a -> Type
typ'' r ctx x = case typ r ctx x of
                    t'@(TUser _ n) -> case fromJust $ tdefType $ getType r n of
                                           TStruct _ _ -> t'
                                           t           -> typ'' r ctx t
                    t         -> t

isBool :: (WithType a) => Refine -> ECtx -> a -> Bool
isBool r ctx a = case typ' r ctx a of
                      TBool _ -> True
                      _       -> False

isBit :: (WithType a) => Refine -> ECtx -> a -> Bool
isBit r ctx a = case typ' r ctx a of
                     TBit _ _ -> True
                     _        -> False

isLocation :: (WithType a) => Refine -> ECtx -> a -> Bool
isLocation r ctx a = case typ' r ctx a of
                          TLocation _ -> True
                          _           -> False

isStruct :: (WithType a) => Refine -> ECtx -> a -> Bool
isStruct r ctx a = case typ' r ctx a of
                        TStruct _ _ -> True
                        _           -> False

isArray :: (WithType a) => Refine -> ECtx -> a -> Bool
isArray r ctx a = case typ' r ctx a of
                       TArray _ _ _ -> True
                       _            -> False


matchType :: (MonadError String me, WithType a, WithPos a, WithType b) => Refine -> ECtx -> a -> b -> me ()
matchType r ctx x y = assertR r (matchType' r ctx x y) (pos x) $ "Incompatible types " ++ show (typ r ctx x) ++ " and " ++ show (typ r ctx y)


matchType' :: (WithType a, WithType b) => Refine -> ECtx -> a -> b -> Bool
matchType' r ctx x y = 
    case (t1, t2) of
         (TLocation _   , TLocation _)    -> True
         (TBool _       , TBool _)        -> True
         (TBit _ w1     , TBit _ w2)      -> w1==w2
         (TInt _        , TInt _)         -> True
         (TString _     , TString _)      -> True
         (TSink _       , TSink _)        -> True
         (TArray _ a1 l1, TArray _ a2 l2) -> matchType' r ctx a1 a2 && l1 == l2
         (TStruct _ cs1 , TStruct _ cs2)  -> (length cs1 == length cs2) &&
                                             (all (\(c1, c2) -> consName c1 == consName c2) $ zip cs1 cs2)
         _                                -> False
    where t1 = typ' r ctx x
          t2 = typ' r ctx y

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
