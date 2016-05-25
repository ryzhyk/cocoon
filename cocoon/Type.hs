{-# LANGUAGE FlexibleContexts #-}

module Type( WithType(..) 
           , typ', typ''
           , isBool, isUInt, isLocation, isStruct
           , matchType
           , typeDomainSize, typeEnumerate) where

import Data.Maybe
import Data.List
import Control.Monad.Except

import Syntax
import NS
import Pos
import Name

class WithType a where
    typ  :: Refine -> ECtx -> a -> Type

instance WithType Type where
    typ _ _ t = t

instance WithType Field where
    typ _ _ = fieldType

instance WithType Expr where
    typ _ ctx           (EVar _ v)         = fieldType $ getVar ctx v
    typ _ (CtxSend _ t) (EDotVar _ v)      = fieldType $ getVar (CtxRole t) v
    typ _ _             (EPacket _)        = TUser nopos packetTypeName
    typ r _             (EApply _ f _)     = funcType $ getFunc r f
    typ r ctx           (EField _ e f)     = let TStruct _ fs = typ' r ctx e  in
                                             fieldType $ fromJust $ find ((== f) . name) fs
    typ _ _             (ELocation _ _ _)  = TLocation nopos
    typ _ _             (EBool _ _)        = TBool nopos
    typ _ _             (EInt _ w _)       = TUInt nopos w
    typ r _             (EStruct _ n _)    = TUser (pos tdef) (name tdef)
                                             where tdef = getType r n
    typ r ctx           (EBinOp _ op e1 e2) = case op of
                                         Eq     -> TBool nopos
                                         Neq    -> TBool nopos
                                         Lt     -> TBool nopos
                                         Gt     -> TBool nopos
                                         Lte    -> TBool nopos
                                         Gte    -> TBool nopos
                                         And    -> TBool nopos
                                         Or     -> TBool nopos
                                         Impl   -> TBool nopos
                                         Equiv  -> TBool nopos
                                         Plus   -> TUInt nopos (max (typeWidth t1) (typeWidth t2))
                                         Minus  -> TUInt nopos (max (typeWidth t1) (typeWidth t2))
                                         ShiftR -> TUInt nopos (typeWidth t1)
                                         ShiftL -> TUInt nopos (typeWidth t1)
                                         Mod    -> t1
                                         Concat -> TUInt nopos (typeWidth t1 + typeWidth t2)
        where t1 = typ' r ctx e1
              t2 = typ' r ctx e2
    typ _ _             (EUnOp _ Not _)     = TBool nopos
    typ _ _             (ESlice _ _ h l)    = TUInt nopos (h-l+1)
    typ r ctx           (ECond _ _ d)       = typ r ctx d

-- Unwrap typedef's down to actual type definition
typ' :: (WithType a) => Refine -> ECtx -> a -> Type
typ' r ctx x = case typ r ctx x of
                    TUser _ n   -> typ' r ctx $ tdefType $ getType r n
                    t           -> t

-- Similar to typ', but does not unwrap the last typedef if it is a struct
typ'' :: (WithType a) => Refine -> ECtx -> a -> Type
typ'' r ctx x = case typ r ctx x of
                    t'@(TUser _ n) -> case tdefType $ getType r n of
                                           TStruct _ _ -> t'
                                           t           -> typ'' r ctx t
                    t         -> t

isBool :: (WithType a) => Refine -> ECtx -> a -> Bool
isBool r ctx a = case typ' r ctx a of
                      TBool _ -> True
                      _       -> False

isUInt :: (WithType a) => Refine -> ECtx -> a -> Bool
isUInt r ctx a = case typ' r ctx a of
                      TUInt _ _ -> True
                      _         -> False

isLocation :: (WithType a) => Refine -> ECtx -> a -> Bool
isLocation r ctx a = case typ' r ctx a of
                          TLocation _ -> True
                          _           -> False

isStruct :: (WithType a) => Refine -> ECtx -> a -> Bool
isStruct r ctx a = case typ' r ctx a of
                        TStruct _ _ -> True
                        _           -> False


matchType :: (MonadError String me, WithType a, WithPos a, WithType b) => Refine -> ECtx -> a -> b -> me ()
matchType r ctx x y = assertR r (matchType' r ctx x y) (pos x) "Incompatible type"

matchType' :: (WithType a, WithType b) => Refine -> ECtx -> a -> b -> Bool
matchType' r ctx x y = 
    case (t1, t2) of
         (TLocation _, TLocation _)     -> True
         (TBool _, TBool _)             -> True
         (TUInt _ w1, TUInt _ w2)       -> w1==w2
         (TStruct _ fs1, TStruct _ fs2) -> (length fs1 == length fs2) &&
                                           (all (uncurry $ matchType' r ctx) $ zip fs1 fs2)
         _                              -> False
    where t1 = typ' r ctx x
          t2 = typ' r ctx y

typeDomainSize :: Refine -> Type -> Integer
typeDomainSize r t = 
    case typ' r undefined t of
         TBool _      -> 2
         TUInt _ w    -> 2^w
         TStruct _ fs -> product $ map (typeDomainSize r . fieldType) fs
         TUser _ _    -> error "Type.typeDomainSize TUser"
         TLocation _  -> error "Not implemented: Type.typeDomainSize TLocation"

typeEnumerate :: Refine -> Type -> [Expr]
typeEnumerate r t = 
    case typ' r undefined t of
         TBool _      -> [EBool nopos False, EBool nopos True]
         TUInt _ w    -> map (EInt nopos w) [0..2^w-1]
         TStruct _ fs -> map (EStruct nopos sname) $ fieldsEnum fs
         TUser _ _    -> error "Type.typeEnumerate TUser"
         TLocation _  -> error "Not implemented: Type.typeEnumerate TLocation"
    where TUser _ sname = typ'' r undefined t
          fieldsEnum []     = [[]]
          fieldsEnum (f:fs) = concatMap (\vs -> map (:vs) $ typeEnumerate r $ fieldType f) $ fieldsEnum fs
