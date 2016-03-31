{-# LANGUAGE FlexibleContexts, RecordWildCards #-}

module Syntax( pktVar
             , Spec(..)
             , Refine(..)
             , errR, assertR
             , Field(..)
             , Role(..)
             , NodeType(..)
             , Node(..)
             , Function(..)
             , Assume(..)
             , Type(..)
             , TypeDef(..)
             , BOp(..)
             , UOp(..)
             , Expr(..)
             , ECtx(..)
             , conj
             , disj
             , Statement(..)
             , statSendsTo) where

import Data.List
import Control.Monad.Except
import Text.PrettyPrint

import Pos
import Name
import Ops
import PP

pktVar = "pkt"

data Spec = Spec [Refine]

data Refine = Refine { refinePos     :: Pos
                     , refineTarget  :: [String]
                     , refineTypes   :: [TypeDef]
                     , refineFuncs   :: [Function]
                     , refineRoles   :: [Role]
                     , refineAssumes :: [Assume]
                     , refineNodes   :: [Node]
                     }

instance WithPos Refine where
    pos = refinePos
    atPos r p = r{refinePos = p}

errR :: (MonadError String me) => Refine -> Pos -> String -> me a
errR r p e = throwError $ spos p ++ ": " ++ e ++ " (when processing refinement at " ++ (spos $ pos r) ++ ")"

assertR :: (MonadError String me) => Refine -> Bool -> Pos -> String -> me ()
assertR r b p m = 
    if b 
       then return ()
       else errR r p m

data Field = Field { fieldPos  :: Pos 
                   , fieldName :: String 
                   , fieldType :: Type
                   }

instance Eq Field where
    (==) f1 f2 = name f1 == name f2 && fieldType f1 == fieldType f2

instance WithPos Field where
    pos = fieldPos
    atPos f p = f{fieldPos = p}

instance WithName Field where
    name = fieldName

instance PP Field where
    pp (Field _ n t) = pp t <+> pp n

instance Show Field where
    show = render . pp

data Role = Role { rolePos       :: Pos
                 , roleName      :: String
                 , roleKeys      :: [Field]
                 , roleKeyRange  :: Expr
                 , roleBody      :: Statement
                 }

instance WithPos Role where
    pos = rolePos
    atPos r p = r{rolePos = p}

instance WithName Role where
    name = roleName

data NodeType = NodeSwitch
              | NodeHost
              deriving Eq

data Node = Node { nodePos   :: Pos
                 , nodeType  :: NodeType
                 , nodeName  :: String
                 , nodePorts :: [(String, String)]
                 }

instance WithPos Node where
    pos = nodePos
    atPos s p = s{nodePos = p}

instance WithName Node where
    name = nodeName

data Assume = Assume { assPos  :: Pos
                     , assVars :: [Field]
                     , assExpr :: Expr
                     }

instance WithPos Assume where
    pos = assPos
    atPos a p = a{assPos = p}

instance PP Assume where 
    pp Assume{..} = pp "assume" <> (parens $ hsep $ punctuate comma $ map pp assVars) <+> pp assExpr

instance Show Assume where
    show = render . pp

data Function = Function { funcPos  :: Pos
                         , funcName :: String
                         , funcArgs :: [Field]
                         , funcType :: Type
                         , funcDom  :: Expr
                         , funcDef  :: Maybe Expr
                         }

instance Eq Function where
    (==) f1 f2 = funcName f1 == funcName f2 &&
                 funcArgs f1 == funcArgs f2 &&
                 funcType f1 == funcType f2 &&
                 funcDom  f1 == funcDom  f2 &&
                 funcDef  f1 == funcDef  f2

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

instance Eq Type where
    (==) (TLocation _)   (TLocation _)   = True
    (==) (TBool _)       (TBool _)       = True
    (==) (TUInt _ w1)    (TUInt _ w2)    = w1 == w2
    (==) (TStruct _ fs1) (TStruct _ fs2) = fs1 == fs2
    (==) (TUser _ n1)    (TUser _ n2)    = n1 == n2
    (==) _               _               = False

instance WithPos Type where
    pos = typePos
    atPos t p = t{typePos = p}

instance PP Type where
    pp (TLocation _)  = pp "Location"
    pp (TBool _)      = pp "bool"
    pp (TUInt _ w)    = pp "uint<" <> pp w <> pp ">" 
    pp (TStruct _ fs) = pp "struct" <> (braces $ hsep $ punctuate comma $ map pp fs)
    pp (TUser _ n)    = pp n

instance Show Type where
    show = render . pp

data TypeDef = TypeDef { tdefPos  :: Pos
                       , tdefName :: String
                       , tdefType :: Type
                       }

instance WithPos TypeDef where
    pos = tdefPos
    atPos t p = t{tdefPos = p}

instance WithName TypeDef where
    name = tdefName

data Expr = EVar      {exprPos :: Pos, exprVar :: String}
          | EPacket   {exprPos :: Pos}
          | EApply    {exprPos :: Pos, exprFunc :: String, exprArgs :: [Expr]}
          | EField    {exprPos :: Pos, exprStruct :: Expr, exprField :: String}
          | ELocation {exprPos :: Pos, exprRole :: String, exprArgs :: [Expr]}
          | EBool     {exprPos :: Pos, exprBVal :: Bool}
          | EInt      {exprPos :: Pos, exprWidth :: Int, exprIVal :: Integer}
          | EStruct   {exprPos :: Pos, exprStructName :: String, exprFields :: [Expr]}
          | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: Expr, exprRight :: Expr}
          | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: Expr}
          | ECond     {exprPos :: Pos, exprCases :: [(Expr, Expr)], exprDefault :: Expr}

instance Eq Expr where
    (==) (EVar      _ k1)        (EVar      _ k2)        = k1 == k2
    (==) (EPacket   _)           (EPacket   _)           = True
    (==) (EApply    _ f1 as1)    (EApply    _ f2 as2)    = (f1 == f2) && (as1 == as2)
    (==) (EField    _ s1 f1)     (EField    _ s2 f2)     = (s1 == s2) && (f1 == f2)
    (==) (ELocation _ r1 as1)    (ELocation _ r2 as2)    = (r1 == r2) && (as1 == as2)
    (==) (EBool     _ v1)        (EBool     _ v2)        = v1 == v2
    (==) (EInt      _ w1 v1)     (EInt      _ w2 v2)     = w1 == w2 && v1 == v2
    (==) (EStruct   _ s1 fs1)    (EStruct   _ s2 fs2)    = (s1 == s2) && (fs1 == fs2)
    (==) (EBinOp    _ op1 l1 r1) (EBinOp    _ op2 l2 r2) = (op1 == op2) && (l1 == l2) && (r1 == r2)
    (==) (EUnOp     _ op1 e1)    (EUnOp     _ op2 e2)    = (op1 == op2) && (e1 == e2)
    (==) (ECond     _ cs1 d1)    (ECond     _ cs2 d2)    = (cs1 == cs2) && (d1 == d2)
    (==) _                       _                       = False

instance WithPos Expr where
    pos = exprPos
    atPos e p = e{exprPos = p}

instance PP Expr where
    pp (EVar _ v)          = pp v
    pp (EPacket _)         = pp pktVar
    pp (EApply _ f as)     = pp f <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EField _ s f)      = pp s <> char '.' <> pp f
    pp (ELocation _ r as)  = pp r <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EBool _ True)      = pp "true"
    pp (EBool _ False)     = pp "false"
    pp (EInt _ w v)        = pp w <> pp "'d" <> pp v
    pp (EStruct _ s fs)    = pp s <> (braces $ hsep $ punctuate comma $ map pp fs)
    pp (EBinOp _ op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp _ op e)      = parens $ pp op  <> pp e
    pp (ECond _ cs d)      = pp "case" <+> (braces $ hsep $ (map (\(c,v) -> pp c <> colon <+> pp v <> semi) cs) ++ [pp "default" <> colon <+> pp d <> semi])

instance Show Expr where
    show = render . pp

conj :: [Expr] -> Expr
conj []     = EBool nopos True
conj [e]    = e
conj (e:es) = EBinOp nopos And e (conj es)

disj :: [Expr] -> Expr
disj []     = EBool nopos False
disj [e]    = e
disj (e:es) = EBinOp nopos Or e (disj es)



data ECtx = CtxRole   Role
          | CtxAssume Assume
          | CtxFunc   Function
     
instance Show ECtx where
    show (CtxRole r)   = "role " ++ name r
    show (CtxAssume a) = "assume " ++ show a
    show (CtxFunc f)   = "function " ++ name f

data Statement = SSeq  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | SPar  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | SITE  {statPos :: Pos, statCond :: Expr, statThen :: Statement, statElse :: Maybe Statement}
               | STest {statPos :: Pos, statCond :: Expr}
               | SSet  {statPos :: Pos, statLVal :: Expr, statRVal :: Expr}
               | SSend {statPos :: Pos, statDst :: Expr}


statSendsTo :: Statement -> [Expr]
statSendsTo st = nub $ statSendsTo' st

statSendsTo' :: Statement -> [Expr]
statSendsTo' (SSeq  _ s1 s2)   = statSendsTo' s1 ++ statSendsTo' s2
statSendsTo' (SPar  _ s1 s2)   = statSendsTo' s1 ++ statSendsTo' s2
statSendsTo' (SITE  _ _ s1 s2) = statSendsTo' s1 ++ (maybe [] statSendsTo' s2)
statSendsTo' (STest _ _)       = []
statSendsTo' (SSet  _ _ _)     = []
statSendsTo' (SSend _ loc)     = [loc]

instance WithPos Statement where
    pos = statPos
    atPos s p = s{statPos = p}

instance PP Statement where
    pp (SSeq _ s1 s2) = lbrace 
                        $$ (nest' $ (pp s1 <> semi) $$ pp s2)
                        $$ rbrace
    pp (SPar _ s1 s2) = lbrace 
                        $$ (nest' $ pp s1 $$ pp "|" $$ pp s2)
                        $$ rbrace
    pp (SITE _ c t e) = (pp "if" <+> pp c <+> pp "then")
                        $$ (nest' $ pp t)
                        $$ (maybe empty (\e' -> pp "else" $$ (nest' $ pp e')) e)
    pp (STest _ c)    = pp "filter" <+> pp c
    pp (SSet _ l r)   = pp l <+> pp ":=" <+> pp r
    pp (SSend _ d)    = pp "send" <+> pp d

instance Show Statement where
    show = render . pp

