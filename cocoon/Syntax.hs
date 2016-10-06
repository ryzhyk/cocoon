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
{-# LANGUAGE FlexibleContexts, RecordWildCards #-}

module Syntax( pktVar
             , Spec(..)
             , Refine(..)
             , errR, assertR
             , Field(..)
             , Role(..)
             , roleLocals
             , roleForkVars
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
             , isRoleCtx
             , ctxRole
             , ctxForkVars
             , conj
             , disj
             , Statement(..)
             , statLocals) where

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

instance PP Refine where
    pp Refine{..} = (pp "refine" <+> (hcat $ punctuate comma $ map pp refineTarget) <+> lbrace)
                    $$
                    (nest' $ (vcat $ map pp refineTarget)
                             $$
                             (vcat $ map pp refineFuncs)
                             $$
                             (vcat $ map pp refineAssumes)
                             $$
                             (vcat $ map pp refineRoles)
                             $$
                             (vcat $ map pp refineNodes))
                    $$
                    rbrace

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
                 , rolePktGuard  :: Expr
                 , roleStateVars :: [Field]
                 , roleBody      :: Statement
                 }

instance WithPos Role where
    pos = rolePos
    atPos r p = r{rolePos = p}

instance WithName Role where
    name = roleName

instance PP Role where
    pp Role{..} = (pp "role" <+> pp roleName <+> (brackets $ hcat $ punctuate comma $ map pp roleKeys)
                   <> pp "|" <+> pp roleKeyRange <+> pp "/" <+> pp rolePktGuard <+> pp "=")
                  $$
                  (vcat $ map ((pp "var" <+>) . pp) roleStateVars)
                  $$
                  (nest' $ pp roleBody)

data NodeType = NodeSwitch
              | NodeHost
              deriving Eq

roleLocals :: Role -> [Field]
roleLocals role = statLocals $ roleBody role

roleForkVars :: Role -> [Field]
roleForkVars role = statForkVarsRec $ roleBody role

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

instance PP Node where
    pp Node{..} = case nodeType of
                       NodeSwitch -> pp "switch"
                       NodeHost   -> pp "host"
                  <+>
                  (parens $ hcat $ punctuate comma $ map (\(i,o) -> parens $ pp i <> comma <+> pp o) nodePorts)


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

instance PP Function where
    pp Function{..} = (pp "function" <+> pp funcName <+> (parens $ hcat $ punctuate comma $ map pp funcArgs) <> colon <+> pp funcType <>
                       maybe empty (\_ -> pp "=") funcDef)
                      $$
                      maybe empty (nest' . pp) funcDef

data Type = TLocation {typePos :: Pos}
          | TBool     {typePos :: Pos}
          | TUInt     {typePos :: Pos, typeWidth :: Int}
          | TArray    {typePos :: Pos, typeElemType :: Type, typeLength :: Int}
          | TStruct   {typePos :: Pos, typeFields :: [Field]}
          | TUser     {typePos :: Pos, typeName :: String}

instance Eq Type where
    (==) (TLocation _)    (TLocation _)    = True
    (==) (TBool _)        (TBool _)        = True
    (==) (TUInt _ w1)     (TUInt _ w2)     = w1 == w2
    (==) (TArray _ t1 l1) (TArray _ t2 l2) = t1 == t2 && l1 == l2
    (==) (TStruct _ fs1)  (TStruct _ fs2)  = fs1 == fs2
    (==) (TUser _ n1)     (TUser _ n2)     = n1 == n2
    (==) _               _                 = False

instance WithPos Type where
    pos = typePos
    atPos t p = t{typePos = p}

instance PP Type where
    pp (TLocation _)  = pp "Location"
    pp (TBool _)      = pp "bool"
    pp (TUInt _ w)    = pp "uint<" <> pp w <> pp ">" 
    pp (TArray _ t l) = brackets $ pp t <> semi <+> pp l
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
          | EDotVar   {exprPos :: Pos, exprVar :: String}
          | EPacket   {exprPos :: Pos}
          | EApply    {exprPos :: Pos, exprFunc :: String, exprArgs :: [Expr]}
          | EBuiltin  {exprPos :: Pos, exprFunc :: String, exprArgs :: [Expr]}
          | EField    {exprPos :: Pos, exprStruct :: Expr, exprField :: String}
          | ELocation {exprPos :: Pos, exprRole :: String, exprArgs :: [Expr]}
          | EBool     {exprPos :: Pos, exprBVal :: Bool}
          | EInt      {exprPos :: Pos, exprWidth :: Int, exprIVal :: Integer}
          | EStruct   {exprPos :: Pos, exprStructName :: String, exprFields :: [Expr]}
          | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: Expr, exprRight :: Expr}
          | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: Expr}
          | ESlice    {exprPos :: Pos, exprOp :: Expr, exprH :: Int, exprL :: Int}
          | ECond     {exprPos :: Pos, exprCases :: [(Expr, Expr)], exprDefault :: Expr}

instance Eq Expr where
    (==) (EVar      _ k1)        (EVar      _ k2)        = k1 == k2
    (==) (EDotVar   _ k1)        (EDotVar   _ k2)        = k1 == k2
    (==) (EPacket   _)           (EPacket   _)           = True
    (==) (EApply    _ f1 as1)    (EApply    _ f2 as2)    = (f1 == f2) && (as1 == as2)
    (==) (EBuiltin  _ f1 as1)    (EBuiltin  _ f2 as2)    = (f1 == f2) && (as1 == as2)
    (==) (EField    _ s1 f1)     (EField    _ s2 f2)     = (s1 == s2) && (f1 == f2)
    (==) (ELocation _ r1 as1)    (ELocation _ r2 as2)    = (r1 == r2) && (as1 == as2)
    (==) (EBool     _ v1)        (EBool     _ v2)        = v1 == v2
    (==) (EInt      _ w1 v1)     (EInt      _ w2 v2)     = w1 == w2 && v1 == v2
    (==) (EStruct   _ s1 fs1)    (EStruct   _ s2 fs2)    = (s1 == s2) && (fs1 == fs2)
    (==) (EBinOp    _ op1 l1 r1) (EBinOp    _ op2 l2 r2) = (op1 == op2) && (l1 == l2) && (r1 == r2)
    (==) (EUnOp     _ op1 e1)    (EUnOp     _ op2 e2)    = (op1 == op2) && (e1 == e2)
    (==) (ESlice    _ e1 h1 l1)  (ESlice    _ e2 h2 l2)  = (e1 == e2) && (h1 == h2) && (l1 == l2)
    (==) (ECond     _ cs1 d1)    (ECond     _ cs2 d2)    = (cs1 == cs2) && (d1 == d2)
    (==) _                       _                       = False

instance WithPos Expr where
    pos = exprPos
    atPos e p = e{exprPos = p}

instance PP Expr where
    pp (EVar _ v)          = pp v
    pp (EDotVar _ v)       = char '.' <> pp v
    pp (EPacket _)         = pp pktVar
    pp (EApply _ f as)     = pp f <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EBuiltin _ f as)   = pp f <> char '!' <>(parens $ hsep $ punctuate comma $ map pp as)
    pp (EField _ s f)      = pp s <> char '.' <> pp f
    pp (ELocation _ r as)  = pp r <> (brackets $ hsep $ punctuate comma $ map pp as)
    pp (EBool _ True)      = pp "true"
    pp (EBool _ False)     = pp "false"
    pp (EInt _ w v)        = pp w <> pp "'d" <> pp v
    pp (EStruct _ s fs)    = pp s <> (braces $ hsep $ punctuate comma $ map pp fs)
    pp (EBinOp _ op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp _ op e)      = parens $ pp op <+> pp e
    pp (ESlice _ e h l)    = pp e <> (brackets $ pp h <> colon <> pp l)
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



data ECtx = CtxAssume Assume
          | CtxFunc   Function
          | CtxRole   Role
          | CtxSend   ECtx Role
          | CtxFork   ECtx [Field]
     
instance Show ECtx where
    show (CtxAssume a)  = "assume " ++ show a
    show (CtxFunc f)    = "function " ++ name f
    show (CtxRole r)    = "role " ++ name r
    show (CtxSend f t)  = "send " ++ ("(" ++ show f ++ ")") ++ " " ++ name t
    show (CtxFork c vs) = "fork " ++ ("(" ++ show c ++ ")") ++ " " ++ show vs

isRoleCtx :: ECtx -> Bool
isRoleCtx (CtxRole _)   = True
isRoleCtx (CtxSend _ _) = True
isRoleCtx (CtxFork _ _) = True
isRoleCtx _             = False

ctxRole :: ECtx -> Role
ctxRole (CtxRole rl)   = rl
ctxRole (CtxSend c _)  = ctxRole c
ctxRole (CtxFork c _)  = ctxRole c
ctxRole c              = error $ "ctxRole " ++ show c

ctxForkVars :: ECtx -> [Field]
ctxForkVars (CtxFork c vs) = vs ++ ctxForkVars c
ctxForkVars (CtxSend c _)  = ctxForkVars c
ctxForkVars _              = []

data Statement = SSeq    {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | SPar    {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               | SITE    {statPos :: Pos, statCond :: Expr, statThen :: Statement, statElse :: Maybe Statement}
               | STest   {statPos :: Pos, statCond :: Expr}
               | SSet    {statPos :: Pos, statLVal :: Expr, statRVal :: Expr}
               | SSend   {statPos :: Pos, statDst  :: Expr}
               | SSendND {statPos :: Pos, statSndRole :: String, statCond :: Expr}
               | SHavoc  {statPos :: Pos, statLVal :: Expr}
               | SAssume {statPos :: Pos, statCond :: Expr}
               | SLet    {statPos :: Pos, statVType :: Type, statVName :: String, statVal :: Expr}
               | SFork   {statPos :: Pos, statFrkVars :: [Field], statCond :: Expr, statFrkBody :: Statement}

statLocals :: Statement -> [Field]
statLocals (SSeq _ l r)      = statLocals l ++ statLocals r
statLocals (SPar _ l r)      = statLocals l ++ statLocals r
statLocals (SITE _ _ t me)   = statLocals t ++ maybe [] statLocals me
statLocals (STest _ _)       = []
statLocals (SSet _ _ _)      = []
statLocals (SSend _ _)       = []
statLocals (SSendND _ _ _)   = []
statLocals (SHavoc _ _)      = []
statLocals (SAssume _ _)     = []
statLocals (SLet p t n _)    = [Field p n t]
statLocals (SFork _ _ _ _)   = []

statForkVarsRec :: Statement -> [Field]
statForkVarsRec (SSeq _ l r)      = statForkVarsRec l ++ statForkVarsRec r
statForkVarsRec (SPar _ l r)      = statForkVarsRec l ++ statForkVarsRec r
statForkVarsRec (SITE _ _ t me)   = statForkVarsRec t ++ maybe [] statForkVarsRec me
statForkVarsRec (STest _ _)       = []
statForkVarsRec (SSet _ _ _)      = []
statForkVarsRec (SSend _ _)       = []
statForkVarsRec (SSendND _ _ _)   = []
statForkVarsRec (SHavoc _ _)      = []
statForkVarsRec (SAssume _ _)     = []
statForkVarsRec (SLet _ _ _ _)    = []
statForkVarsRec (SFork _ vs _ b)  = vs ++ statForkVarsRec b

instance WithPos Statement where
    pos = statPos
    atPos s p = s{statPos = p}

instance PP Statement where
    pp (SSeq _ s1 s2)   = lbrace 
                          $$ (nest' $ (pp s1 <> semi) $$ pp s2)
                          $$ rbrace
    pp (SPar _ s1 s2)   = lbrace 
                          $$ (nest' $ pp s1 $$ pp "|" $$ pp s2)
                          $$ rbrace
    pp (SITE _ c t e)   = (pp "if" <+> pp c <+> pp "then")
                          $$ (nest' $ pp t)
                          $$ (maybe empty (\e' -> pp "else" $$ (nest' $ pp e')) e)
    pp (STest _ c)      = pp "filter" <+> pp c
    pp (SSet _ l r)     = pp l <+> pp ":=" <+> pp r
    pp (SSend _ d)      = pp "send" <+> pp d
    pp (SSendND _ rl c) = pp "?send" <+> pp rl <> (brackets $ pp c)
    pp (SHavoc _ e)     = pp "havoc" <+> pp e
    pp (SAssume _ e)    = pp "assume" <+> pp e
    pp (SLet _ t n v)   = pp "let" <+> pp t <+> pp n <+> pp "=" <+> pp v
    pp (SFork _ vs c b) = pp "fork" <+> (parens $ (hsep $ punctuate (pp ",") $ map pp vs) <+> pp "|" <+> pp c) <+> pp b

instance Show Statement where
    show = render . pp

