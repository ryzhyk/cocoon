{-# LANGUAGE FlexibleContexts #-}

module Type( typ', typ''
           , isBool, isUInt, isLocation
           , matchType) where

import Data.Maybe
import Data.List
import Control.Monad.Except

import Syntax
import NS
import Util
import Pos
import Name

class WithType a where
    typ  :: Refine -> Role -> a -> Type

instance WithType Type where
    typ _ _ t = t

instance WithType Field where
    typ _ _ = fieldType

instance WithType Expr where
    typ r role (EKey _ k)          = fieldType $ getKey role k
    typ r _    (EPacket _)         = tdefType $ getType r packetTypeName
    typ r _    (EApply _ f _)      = funcType $ getFunc r f
    typ r role (EField _ e f)      = let TStruct _ fs = typ' r role e
                                     in fieldType $ fromJust $ find ((== f) . name) fs
    typ _ _    (ELocation _ _ _)   = TLocation nopos
    typ _ _    (EBool _ _)         = TBool nopos
    typ _ _    (EInt _ v)          = TUInt nopos (bitWidth v)
    typ r _    (EStruct _ n _)     = TUser (pos tdef) (name tdef)
                                     where tdef = getType r n
    typ r role (EBinOp _ op e1 e2) = case op of
                                          Eq   -> TBool nopos
                                          Lt   -> TBool nopos
                                          Gt   -> TBool nopos
                                          Lte  -> TBool nopos
                                          Gte  -> TBool nopos
                                          And  -> TBool nopos
                                          Or   -> TBool nopos
                                          Plus -> TUInt nopos (max (typeWidth t1) (typeWidth t2))
                                          Mod  -> t1
        where t1 = typ' r role e1
              t2 = typ' r role e2
    typ _ _    (EUnOp _ Not _)    = TBool nopos
    typ r role (ECond _ _ d)      = typ r role d

-- Unwrap typedef's down to actual type definition
typ' :: (WithType a) => Refine -> Role -> a -> Type
typ' r role x = case typ r role x of
                     TUser _ n -> typ' r role $ tdefType $ getType r n
                     t         -> t

-- Similar to typ', but does not unwrap the last typedef if it is a struct
typ'' :: (WithType a) => Refine -> Role -> a -> Type
typ'' r role x = case typ r role x of
                      t'@(TUser _ n) -> case tdefType $ getType r n of
                                             TStruct _ _ -> t'
                                             t           -> typ'' r role t
                      t         -> t

isBool :: (WithType a) => Refine -> Role -> a -> Bool
isBool r role a = case typ' r role a of
                       TBool _ -> True
                       _       -> False

isUInt :: (WithType a) => Refine -> Role -> a -> Bool
isUInt r role a = case typ' r role a of
                       TUInt _ _ -> True
                       _         -> False

isLocation :: (WithType a) => Refine -> Role -> a -> Bool
isLocation r role a = case typ' r role a of
                           TLocation _ -> True
                           _           -> False

matchType :: (MonadError String me, WithType a, WithPos a, WithType b) => Refine -> Role -> a -> b -> me ()
matchType r role x y = assertR r (matchType' r role x y) (pos x) "Incompatible type"

matchType' :: (WithType a, WithType b) => Refine -> Role -> a -> b -> Bool
matchType' r role x y = 
    case (t1, t2) of
         (TLocation _, TLocation _)     -> True
         (TBool _, TBool _)             -> True
         (TUInt _ w1, TUInt _ w2)       -> w1==w2
         (TStruct _ fs1, TStruct _ fs2) -> (length fs1 == length fs2) &&
                                           (all (uncurry $ matchType' r role) $ zip fs1 fs2)
    where t1 = typ' r role x
          t2 = typ' r role y
