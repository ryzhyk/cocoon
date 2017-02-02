{-# LANGUAGE FlexibleContexts, RecordWildCards #-}

module Syntax( pktVar
             , Spec(..)
             , Refine(..)
             , errR, assertR
             , Field(..)
             , Role(..)
             , Relation(..)
             , Constraint(..)
             , Constructor(..)
             , Rule(..)
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
             , disj) where

import Control.Monad.Except
import Text.PrettyPrint

import Pos
import Name
import Ops
import PP

pktVar = "pkt"

data Spec = Spec [Refine]

data Refine = Refine { refinePos       :: Pos
                     , refineTarget    :: [String]
                     , refineTypes     :: [TypeDef]
                     , refineFunctions :: [Function]
                     , refineRelations :: [Relation]
                     , refineAssumes   :: [Assume]
                     , refineRoles     :: [Role]
                     , refineNodes     :: [Node]
                     }

instance WithPos Refine where
    pos = refinePos
    atPos r p = r{refinePos = p}

instance PP Refine where
    pp Refine{..} = (pp "refine" <+> (hcat $ punctuate comma $ map pp refineTarget) <+> lbrace)
                    $$
                    (nest' $ (vcat $ map pp refineTarget)
                             $$
                             (vcat $ map pp refineFunctions)
                             $$
                             (vcat $ map pp refineRelations)
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

instance WithPos Field where
    pos = fieldPos
    atPos f p = f{fieldPos = p}

instance WithName Field where
    name = fieldName

instance PP Field where
    pp (Field _ n t) = pp n <> pp ":" <+>pp t

instance Show Field where
    show = render . pp

data Role = Role { rolePos       :: Pos
                 , roleName      :: String
                 , roleKeys      :: [Field]
                 , roleKeyRange  :: Expr
                 , rolePktGuard  :: Expr
                 , roleBody      :: Expr
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
                  (nest' $ pp roleBody)

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

instance PP Node where
    pp Node{..} = case nodeType of
                       NodeSwitch -> pp "switch"
                       NodeHost   -> pp "host"
                  <+>
                  (parens $ hcat $ punctuate comma $ map (\(i,o) -> parens $ pp i <> comma <+> pp o) nodePorts)

data Constraint = PrimaryKey {constrPos :: Pos, constrArgs :: [String]}
                | ForeignKey {constrPos :: Pos, constrFields :: [Expr], constrForeign :: String, constrFArgs :: [String]}
                | Unique     {constrPos :: Pos, constrFields :: [Expr]}
                | Check      {constrPos :: Pos, constrCond :: Expr}

instance WithPos Constraint where
    pos = constrPos
    atPos c p = c{constrPos = p}


instance PP Constraint where
    pp (PrimaryKey _ as)       = pp "primary key" <+> (parens $ hsep $ punctuate comma $ map pp as)
    pp (ForeignKey _ as f fas) = pp "foreign key" <+> (parens $ hsep $ punctuate comma $ map pp as) <+> pp "references" 
                                 <+> pp f <+> (parens $ hsep $ punctuate comma $ map pp fas)
    pp (Unique _ as)           = pp "unique" <+> (parens $ hsep $ punctuate comma $ map pp as)
    pp (Check _ e)             = pp "check" <+> pp e
   

data Relation = Relation { relPos  :: Pos
                         , relName :: String
                         , relArgs :: [Field]
                         , relConstraints :: [Constraint]
                         , relDef  :: Maybe [Rule]}

instance WithPos Relation where
    pos = relPos
    atPos r p = r{relPos = p}

instance PP Relation where
    pp Relation{..} = pp "relation" <+> pp relName <+> 
                      (parens $ hsep $ punctuate comma $ map pp relArgs ++ map pp relConstraints) <+>
                      (maybe empty (\_ -> pp "=") relDef) $$
                      (maybe empty (vcat . map (ppRule relName)) relDef)

data Rule = Rule { rulePos :: Pos
                 , ruleLHS :: [Expr]
                 , ruleRHS :: [Expr]}

ppRule :: String -> Rule -> Doc
ppRule rel Rule{..} = pp rel <> (parens $ hsep $ punctuate comma $ map pp ruleLHS) <+> pp ":-" <+> (hsep $ punctuate comma $ map pp ruleRHS)

instance WithPos Rule where
    pos = rulePos
    atPos r p = r{rulePos = p}

data Assume = Assume { assPos  :: Pos
                     , assArgs :: [Field]
                     , assExpr :: Expr
                     }

instance WithPos Assume where
    pos = assPos
    atPos a p = a{assPos = p}

instance PP Assume where 
    pp Assume{..} = pp "assume" <+> (parens $ hsep $ punctuate comma $ map pp assArgs) <+> pp assExpr

instance Show Assume where
    show = render . pp

data Function = Function { funcPos  :: Pos
                         , funcName :: String
                         , funcArgs :: [Field]
                         , funcType :: Maybe Type
                         , funcDom  :: Expr
                         , funcDef  :: Expr
                         }

instance WithPos Function where
    pos = funcPos
    atPos f p = f{funcPos = p}

instance WithName Function where
    name = funcName

instance PP Function where
    pp Function{..} = (pp "function" <+> pp funcName <+> (parens $ hcat $ punctuate comma $ map pp funcArgs) 
                      <> (maybe empty ((colon <+>) . pp) funcType) <>
                       pp "=")
                      $$
                      (nest' $ pp funcDef)

data Constructor = Constructor { consPos :: Pos
                               , consName :: String
                               , consArgs :: [Field] }

instance WithPos Constructor where
    pos = consPos
    atPos c p = c{consPos = p}

instance PP Constructor where
    pp Constructor{..} = pp consName <> (braces $ hsep $ punctuate comma $ map pp consArgs)

instance Show Constructor where
    show = render . pp

data Type = TLocation {typePos :: Pos}
          | TBool     {typePos :: Pos}
          | TInt      {typePos :: Pos}
          | TString   {typePos :: Pos}
          | TBit      {typePos :: Pos, typeWidth :: Int}
          | TArray    {typePos :: Pos, typeElemType :: Type, typeLength :: Int}
          | TStruct   {typePos :: Pos, typeCons :: [Constructor]}
          | TTuple    {typePos :: Pos, typeArgs :: [Type]}
          | TUser     {typePos :: Pos, typeName :: String}

instance WithPos Type where
    pos = typePos
    atPos t p = t{typePos = p}

instance PP Type where
    pp (TLocation _)    = pp "Location"
    pp (TBool _)        = pp "bool"
    pp (TInt _)         = pp "int" 
    pp (TString _)      = pp "string" 
    pp (TBit _ w)       = pp "bit<" <> pp w <> pp ">" 
    pp (TArray _ t l)   = brackets $ pp t <> semi <+> pp l
    pp (TStruct _ cons) = vcat $ punctuate (char '|') $ map pp cons
    pp (TTuple _ as)    = parens $ hsep $ punctuate comma $ map pp as
    pp (TUser _ n)      = pp n

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
          | EBuiltin  {exprPos :: Pos, exprFunc :: String, exprArgs :: [Expr]}
          | EField    {exprPos :: Pos, exprStruct :: Expr, exprField :: String}
          | ELocation {exprPos :: Pos, exprRole :: String, exprArgs :: [Expr]}
          | EBool     {exprPos :: Pos, exprBVal :: Bool}
          | EInt      {exprPos :: Pos, exprIVal :: Integer}
          | EString   {exprPos :: Pos, exprString :: String}
          | EBit      {exprPos :: Pos, exprWidth :: Int, exprIVal :: Integer}
          | EStruct   {exprPos :: Pos, exprConstructor :: String, exprFields :: [Expr]}
          | ETuple    {exprPos :: Pos, exprFields :: [Expr]}
          | ESlice    {exprPos :: Pos, exprOp :: Expr, exprH :: Int, exprL :: Int}
          | EMatch    {exprPos :: Pos, exprMatchExpr :: Expr, exprCases :: [(Expr, Expr)], exprDefault :: Maybe Expr}
          | ELet      {exprPos :: Pos, exprLVal :: Expr, exprRVal :: Expr}
          | ESeq      {exprPos :: Pos, exprLeft :: Expr, exprRight :: Expr}
          | EPar      {exprPos :: Pos, exprLeft :: Expr, exprRight :: Expr}
          | EITE      {exprPos :: Pos, exprCond :: Expr, exprThen :: Expr, exprElse :: Maybe Expr}
          | ETest     {exprPos :: Pos, exprCond :: Expr}
          | ESet      {exprPos :: Pos, exprLVal :: Expr, exprRVal :: Expr}
          | ESend     {exprPos :: Pos, exprDst  :: Expr}
          | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: Expr, exprRight :: Expr}
          | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: Expr}
          | ENDLet    {exprPos :: Pos, exprLetVars :: [String], exprLetCond :: Expr}
          | EFork     {exprPos :: Pos, exprFrkVars :: [String], exprFrkCond :: Expr, exprFrkBody :: Expr}
          | EPHolder  {exprPos :: Pos}

instance WithPos Expr where
    pos = exprPos
    atPos e p = e{exprPos = p}

instance PP Expr where
    pp (EVar _ v)          = pp v
    pp (EPacket _)         = pp pktVar
    pp (EApply _ f as)     = pp f <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EBuiltin _ f as)   = pp f <> char '!' <>(parens $ hsep $ punctuate comma $ map pp as)
    pp (EField _ s f)      = pp s <> char '.' <> pp f
    pp (ELocation _ r as)  = pp r <> (brackets $ hsep $ punctuate comma $ map pp as)
    pp (EBool _ True)      = pp "true"
    pp (EBool _ False)     = pp "false"
    pp (EInt _ v)          = pp v
    pp (EString _ s)       = pp s
    pp (EBit _ w v)        = pp w <> pp "'d" <> pp v
    pp (EStruct _ s fs)    = pp s <> (braces $ hsep $ punctuate comma $ map pp fs)
    pp (ETuple _ fs)       = parens $ hsep $ punctuate comma $ map pp fs
    pp (ESlice _ e h l)    = pp e <> (brackets $ pp h <> colon <> pp l)
    pp (EMatch _ e cs d)   = pp "match" <+> pp e <+> (braces $ vcat 
                                                       $ punctuate comma 
                                                       $ (map (\(c,v) -> pp c <> colon <+> pp v) cs) ++ 
                                                         (maybe [] (\x -> [pp "default" <> colon <+> pp x]) d))
    pp (ELet _ l r)        = pp "let" <+> pp l <+> pp "=" <+> pp r
    pp (ESeq _ l r)        = (pp l <> semi) $$ pp r
    pp (EPar _ l r)        = (pp l <> pp "|" ) $$ pp r
    pp (EITE _ c t me)     = (pp "if" <+> pp c <+> lbrace)
                             $$
                             (nest' $ pp t)
                             $$
                             rbrace <+> (maybe empty (\e -> (pp "else" <+> lbrace) $$ (nest' $ pp e) $$ rbrace) me)
    pp (ETest _ c)         = pp "filter" <+> pp c
    pp (ESet _ l r)        = pp l <+> pp ":=" <+> pp r
    pp (ESend  _ e)        = pp "send" <+> pp e
    pp (EBinOp _ op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp _ op e)      = parens $ pp op <+> pp e
    pp (ENDLet _ vs c)     = pp "let" <+>  (hsep $ punctuate comma $ map pp vs) <+> pp "|" <+> pp c
    pp (EFork _ vs c b)    = (pp "fork" <+> (hsep $ punctuate comma $ map pp vs) <+> pp "|" <+> pp c) $$ (nest' $ pp b)
    pp (EPHolder _)        = pp "_"

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

data ECtx = CtxAssume   Assume
          | CtxRule     Relation Rule
          | CtxFunc     Function
          | CtxRole     Role
          | CtxLet      ECtx [Field]
          | CtxFork     ECtx [Field]
