module Syntax( Spec(..)
             , Refine(..)
             , Field(..)
             , Role(..)
             , Function(..)
             , Type(..)
             , TypeDef(..)
             , BOp(..)
             , UOp(..)
             , Expr(..)
             , Statement(..)) where

import Pos
import Name

data Spec = Spec [Refine]

data Refine = Refine { refinePos    :: Pos
                     , refineTarget :: [String]
                     , refineTypes  :: [TypeDef]
                     , refineFuncs  :: [Function]
                     , refineRoles  :: [Role]
                     }

instance WithPos Refine where
    pos = refinePos
    atPos r p = r{refinePos = p}

data Field = Field { fieldPos  :: Pos 
                   , fieldName :: String 
                   , fieldType :: Type
                   }

instance WithPos Field where
    pos = fieldPos
    atPos f p = f{fieldPos = p}

instance WithName Field where
    name = fieldName

data Role = Role { rolePos       :: Pos
                 , roleName      :: String
                 , roleKeys      :: [Field]
                 , roleKeyRange  :: Expr
                 , roleContains  :: [Expr]
                 , roleBody      :: Statement
                 }

instance WithPos Role where
    pos = rolePos
    atPos r p = r{rolePos = p}

instance WithName Role where
    name = roleName

data Function = Function { funcPos  :: Pos
                         , funcName :: String
                         , funcArgs :: [Field]
                         , funcType :: Type
                         }

instance WithPos Function where
    pos = funcPos
    atPos f p = f{funcPos = p}

instance WithName Function where
    name = funcName

data Type = TLocation {typePos :: Pos}
          | TBool     {typePos :: Pos}
          | TUInt     {typePos :: Pos, typeWidth :: Int}
          | TStruct   {typePos :: Pos, typeFields :: [Field]}
          | TUser     {typePos :: Pos, typeName :: String}

instance WithPos Type where
    pos = typePos
    atPos t p = t{typePos = p}

data TypeDef = TypeDef { tdefPos  :: Pos
                       , tdefName :: String
                       , tdefType :: Type
                       }

instance WithPos TypeDef where
    pos = tdefPos
    atPos t p = t{tdefPos = p}

instance WithName TypeDef where
    name = tdefName

data BOp = Eq
         | And
         | Or
         | Plus
         | Mod

data UOp = Not

data Expr = EKey      {exprPos :: Pos, exprKey :: String}
          | EPacket   {exprPos :: Pos}
          | EApply    {exprPos :: Pos, exprFunc :: String, exprArgs :: [Expr]}
          | EField    {exprPos :: Pos, exprStruct :: Expr, exprField :: String}
          | ELocation {exprPos :: Pos, exprRole :: String, exprArgs :: [Expr]}
          | EBool     {exprPos :: Pos, exprBVal :: Bool}
          | EInt      {exprPos :: Pos, exprIVal :: Integer}
          | EStruct   {exprPos :: Pos, exprStructName :: String, exprFields :: [Expr]}
          | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: Expr, exprRight :: Expr}
          | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: Expr}
          | ECond     {exprPos :: Pos, exprCases :: [(Expr, Expr)], exprDefault :: Expr}

instance WithPos Expr where
    pos = exprPos
    atPos e p = e{exprPos = p}

data Statement = SSeq  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | SPar  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | STest {statPos :: Pos, statCond :: Expr}
               | SSet  {statPos :: Pos, statLVal :: Expr, statRVal :: Expr}
               | SSend {statPos :: Pos, statDst :: Expr}

instance WithPos Statement where
    pos = statPos
    atPos s p = s{statPos = p}
