{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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
             , Relation(..)
             , relIsView
             , RelAnnotation(..)
             , Constraint(..), isPrimaryKey, isForeignKey, isUnique, isCheck
             , Constructor(..)
             , consType
             , Rule(..)
             , Function(..)
             , Assume(..)
             , Type(..)
             , tLocation, tBool, tInt, tString, tBit, tArray, tStruct, tTuple, tOpaque, tUser, tSink
             , structGetField, structFields, structFieldConstructors, structFieldGuarded, structTypeDef
             , TypeDef(..)
             , BOp(..)
             , UOp(..)
             , ExprNode(..)
             , ENode
             , Expr(..)
             , enode
             , eVar, ePacket, eApply, eField, eLocation, eBool, eTrue, eFalse, eInt, eString, eBit, eStruct, eTuple
             , eSlice, eMatch, eVarDecl, eSeq, ePar, eITE, eDrop, eSet, eSend, eBinOp, eUnOp, eNot, eFork, eFor
             , eWith, eAny, ePHolder, eTyped, eRelPred
             , exprIsRelPred
             , ECtx(..)
             , ctxParent, ctxAncestors
             , ctxIsRelPred, ctxInRelPred
             , ctxIsRuleL, ctxInRuleL
             , ctxIsMatchPat, ctxInMatchPat, ctxInMatchPat'
             , ctxIsSetL, ctxInSetL
             , ctxIsSeq1, ctxInSeq1
             , ctxIsRole, ctxInRole
             , ctxIsTyped
             , conj
             , disj
             , exprSequence) where

import Control.Monad.Except
import Text.PrettyPrint
import Data.Maybe
import Data.List
import Debug.Trace

import Util
import Pos
import Name
import Ops
import PP

pktVar = "pkt"

data Spec = Spec [Refine]

data Refine = Refine { refinePos       :: Pos
                     , refineTarget    :: [String]
                     , refineTypes     :: [TypeDef]
                     , refineState     :: [Field]
                     , refineFuncs     :: [Function]
                     , refineRels      :: [Relation]
                     , refineAssumes   :: [Assume]
                     , refineRoles     :: [Role]
                     }

instance WithPos Refine where
    pos = refinePos
    atPos r p = r{refinePos = p}

instance PP Refine where
    pp Refine{..} = (pp "refine" <+> (hcat $ punctuate comma $ map pp refineTarget) <+> lbrace)
                    $$
                    (nest' $ (vcat $ map pp refineTarget)
                             $$
                             (vcat $ map ((pp "state" <+>) . pp) refineState)
                             $$
                             (vcat $ map pp refineFuncs)
                             $$
                             (vcat $ map pp refineRels)
                             $$
                             (vcat $ map pp refineAssumes)
                             $$
                             (vcat $ map pp refineRoles))
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
    (==) (Field _ n1 t1) (Field _ n2 t2) = n1 == n2 && t1 == t2

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
                 , roleKey       :: String
                 , roleTable     :: String
                 , roleCond      :: Expr
                 , rolePktGuard  :: Expr
                 , roleBody      :: Expr
                 }

instance WithPos Role where
    pos = rolePos
    atPos r p = r{rolePos = p}

instance WithName Role where
    name = roleName

instance PP Role where
    pp Role{..} = (pp "role" <+> pp roleName <+> (brackets $ pp roleKey <+> pp "in" <+> pp roleTable <+> pp "|" <+> pp roleCond <+> pp "/" <+> pp rolePktGuard <+> pp "="))
                  $$
                  (nest' $ pp roleBody)

instance Show Role where
    show = render . pp

data Constraint = PrimaryKey {constrPos :: Pos, constrFields :: [Expr]}
                | ForeignKey {constrPos :: Pos, constrFields :: [Expr], constrForeign :: String, constrFArgs :: [Expr]}
                | Unique     {constrPos :: Pos, constrFields :: [Expr]}
                | Check      {constrPos :: Pos, constrCond :: Expr}
                
isPrimaryKey :: Constraint -> Bool
isPrimaryKey PrimaryKey{} = True
isPrimaryKey _            = False

isForeignKey :: Constraint -> Bool
isForeignKey ForeignKey{} = True
isForeignKey _            = False

isUnique :: Constraint -> Bool
isUnique Unique{} = True
isUnique _        = False

isCheck :: Constraint -> Bool
isCheck Check{} = True
isCheck _       = False

instance WithPos Constraint where
    pos = constrPos
    atPos c p = c{constrPos = p}


instance PP Constraint where
    pp (PrimaryKey _ as)       = pp "primary key" <+> (parens $ hsep $ punctuate comma $ map pp as)
    pp (ForeignKey _ as f fas) = pp "foreign key" <+> (parens $ hsep $ punctuate comma $ map pp as) <+> pp "references" 
                                 <+> pp f <+> (parens $ hsep $ punctuate comma $ map pp fas)
    pp (Unique _ as)           = pp "unique" <+> (parens $ hsep $ punctuate comma $ map pp as)
    pp (Check _ e)             = pp "check" <+> pp e
   
instance Show Constraint where
    show = render . pp

data RelAnnotation = RelPort   {annotPos :: Pos, annotRoles :: (String, String)}
                   | RelSwitch {annotPos :: Pos}

instance WithPos RelAnnotation where
    pos = annotPos
    atPos a p = a{annotPos = p}

instance PP RelAnnotation where
    pp (RelPort _ (inport, outport)) = pp "#switch_port" <> (parens $ pp inport <> comma <> pp outport)
    pp (RelSwitch _)                 = pp "#switch"

instance Show RelAnnotation where
    show = render . pp

data Relation = Relation { relPos         :: Pos
                         , relMutable     :: Bool
                         , relName        :: String
                         , relArgs        :: [Field]
                         , relConstraints :: [Constraint]
                         , relAnnotation  :: Maybe RelAnnotation
                         , relDef         :: Maybe [Rule]}

instance WithPos Relation where
    pos = relPos
    atPos r p = r{relPos = p}

instance WithName Relation where
    name = relName

instance PP Relation where
    pp Relation{..} = (maybe empty pp relAnnotation) $$
                      if' relMutable (pp "state") empty <+>
                      (maybe (pp "table") (\_ -> pp "view") relDef) <+> pp relName <+> 
                      (parens $ hsep $ punctuate comma $ map pp relArgs ++ map pp relConstraints) <+>
                      (maybe empty (\_ -> pp "=") relDef) $$
                      (maybe empty (vcat . map (ppRule relName)) relDef)

instance Show Relation where
    show = render . pp

data Rule = Rule { rulePos :: Pos
                 , ruleLHS :: [Expr]
                 , ruleRHS :: [Expr]}

ppRule :: String -> Rule -> Doc
ppRule rel Rule{..} = pp rel <> (parens $ hsep $ punctuate comma $ map pp ruleLHS) <+> pp ":-" <+> (hsep $ punctuate comma $ map pp ruleRHS)

relIsView :: Relation -> Bool
relIsView = isJust . relDef

instance Show Rule where
    show = render . ppRule ""

instance WithPos Rule where
    pos = rulePos
    atPos r p = r{rulePos = p}

data Assume = Assume { assPos  :: Pos
                     , assVars :: [Field]
                     , assExpr :: Expr
                     }

instance WithPos Assume where
    pos = assPos
    atPos a p = a{assPos = p}

instance PP Assume where 
    pp Assume{..} = pp "assume" <+> (parens $ hsep $ punctuate comma $ map pp assVars) <+> pp assExpr

instance Show Assume where
    show = render . pp

data Function = Function { funcPos  :: Pos
                         , funcPure :: Bool
                         , funcName :: String
                         , funcArgs :: [Field]
                         , funcType :: Type
                         , funcDef  :: Maybe Expr
                         }

instance WithPos Function where
    pos = funcPos
    atPos f p = f{funcPos = p}

instance WithName Function where
    name = funcName

instance PP Function where
    pp Function{..} = ((if' funcPure (pp "function") (pp "procedure")) <+> pp funcName 
                       <+> (parens $ hcat $ punctuate comma $ map pp funcArgs) 
                       <> colon <+> pp funcType 
                       <+> (maybe empty (\_ -> pp "=") funcDef))
                      $$
                       (maybe empty (nest' . pp) funcDef)

instance Show Function where
    show = render . pp

data Constructor = Constructor { consPos :: Pos
                               , consName :: String
                               , consArgs :: [Field] }

instance Eq Constructor where
    (==) (Constructor _ n1 as1) (Constructor _ n2 as2) = n1 == n2 && as1 == as2

instance WithName Constructor where 
    name = consName

instance WithPos Constructor where
    pos = consPos
    atPos c p = c{consPos = p}

instance PP Constructor where
    pp Constructor{..} = pp consName <> (braces $ hsep $ punctuate comma $ map pp consArgs)

instance Show Constructor where
    show = render . pp

consType :: Refine -> String -> TypeDef
consType r c = fromJust 
               $ find (\td -> case tdefType td of
                                   Just (TStruct _ cs) -> any ((==c) . name) cs
                                   _                   -> False)
               $ refineTypes r

data Type = TLocation {typePos :: Pos}
          | TBool     {typePos :: Pos}
          | TInt      {typePos :: Pos}
          | TString   {typePos :: Pos}
          | TBit      {typePos :: Pos, typeWidth :: Int}
          | TArray    {typePos :: Pos, typeElemType :: Type, typeLength :: Int}
          | TStruct   {typePos :: Pos, typeCons :: [Constructor]}
          | TTuple    {typePos :: Pos, typeArgs :: [Type]}
          | TOpaque   {typePos :: Pos, typeName :: String}
          | TUser     {typePos :: Pos, typeName :: String}
          | TSink     {typePos :: Pos}

tLocation = TLocation nopos
tBool     = TBool     nopos
tInt      = TInt      nopos
tString   = TString   nopos
tBit      = TBit      nopos
tArray    = TArray    nopos
tStruct   = TStruct   nopos
tTuple    = TTuple    nopos
tOpaque   = TOpaque   nopos
tUser     = TUser     nopos
tSink     = TSink     nopos

structGetField :: [Constructor] -> String -> Field
structGetField cs f = trace ("structGetField " ++ show f ++ " " ++ show cs) $ fromJust $ find ((==f) . name) $ concatMap consArgs cs

structFields :: [Constructor] -> [Field]
structFields cs = nub $ concatMap consArgs cs

-- All constructors that contain the field
structFieldConstructors :: [Constructor] -> String -> [Constructor]
structFieldConstructors cs f = filter (isJust . find ((==f) . name) . consArgs) cs

-- True iff the field is defined in all constructors
structFieldGuarded :: [Constructor] -> String -> Bool
structFieldGuarded cs f = all (isJust . find ((==f) . name) . consArgs) cs

structTypeDef :: Refine -> Type -> TypeDef
structTypeDef r TStruct{..} = consType r $ name $ head typeCons
structTypeDef _ t           = error $ "structTypeDef " ++ show t

instance Eq Type where
    (==) (TLocation _)    (TLocation _)    = True
    (==) (TBool _)        (TBool _)        = True
    (==) (TInt _)         (TInt _)         = True
    (==) (TString _)      (TString _)      = True
    (==) (TBit _ w1)      (TBit _ w2)      = w1 == w2
    (==) (TArray _ t1 l1) (TArray _ t2 l2) = t1 == t2 && l1 == l2
    (==) (TStruct _ cs1)  (TStruct _ cs2)  = cs1 == cs2
    (==) (TTuple _ ts1)   (TTuple _ ts2)   = ts1 == ts2
    (==) (TOpaque _ n1)   (TOpaque _ n2)   = n1 == n2
    (==) (TUser _ n1)     (TUser _ n2)     = n1 == n2
    (==) (TSink _)        (TSink _)        = True
    (==) _                _                = False

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
    pp (TOpaque _ n)    = pp n
    pp (TUser _ n)      = pp n
    pp (TSink _)        = pp "sink"

instance Show Type where
    show = render . pp

data TypeDef = TypeDef { tdefPos  :: Pos
                       , tdefName :: String
                       , tdefType :: Maybe Type
                       }

instance WithPos TypeDef where
    pos = tdefPos
    atPos t p = t{tdefPos = p}

instance WithName TypeDef where
    name = tdefName

instance PP TypeDef where
    pp TypeDef{..} = pp "typedef" <+> pp tdefName <+> maybe empty ((pp "=" <+>) . pp)  tdefType

instance Show TypeDef where
    show = render . pp

instance Eq TypeDef where
    (==) t1 t2 = name t1 == name t2 && tdefType t1 == tdefType t2

data ExprNode e = EVar      {exprPos :: Pos, exprVar :: String}
                | EPacket   {exprPos :: Pos}
                | EApply    {exprPos :: Pos, exprFunc :: String, exprArgs :: [e]}
                | EField    {exprPos :: Pos, exprStruct :: e, exprField :: String}
                | ELocation {exprPos :: Pos, exprRole :: String, exprKey :: e}
                | EBool     {exprPos :: Pos, exprBVal :: Bool}
                | EInt      {exprPos :: Pos, exprIVal :: Integer}
                | EString   {exprPos :: Pos, exprString :: String}
                | EBit      {exprPos :: Pos, exprWidth :: Int, exprIVal :: Integer}
                | EStruct   {exprPos :: Pos, exprConstructor :: String, exprFields :: [e]}
                | ETuple    {exprPos :: Pos, exprFields :: [e]}
                | ESlice    {exprPos :: Pos, exprOp :: e, exprH :: Int, exprL :: Int}
                | EMatch    {exprPos :: Pos, exprMatchExpr :: e, exprCases :: [(e, e)]}
                | EVarDecl  {exprPos :: Pos, exprVName :: String}
                | ESeq      {exprPos :: Pos, exprLeft :: e, exprRight :: e}
                | EPar      {exprPos :: Pos, exprLeft :: e, exprRight :: e}
                | EITE      {exprPos :: Pos, exprCond :: e, exprThen :: e, exprElse :: Maybe e}
                | EDrop     {exprPos :: Pos}
                | ESet      {exprPos :: Pos, exprLVal :: e, exprRVal :: e}
                | ESend     {exprPos :: Pos, exprDst  :: e}
                | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: e, exprRight :: e}
                | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: e}
                | EFor      {exprPos :: Pos, exprFrkVar :: String, exprTable :: String, exprCond :: e, exprFrkBody :: e}
                | EFork     {exprPos :: Pos, exprFrkVar :: String, exprTable :: String, exprCond :: e, exprFrkBody :: e}
                | EWith     {exprPos :: Pos, exprFrkVar :: String, exprTable :: String, exprCond :: e, exprWithBody :: e, exprDef :: Maybe e}
                | EAny      {exprPos :: Pos, exprFrkVar :: String, exprTable :: String, exprCond :: e, exprWithBody :: e, exprDef :: Maybe e}
                | EPHolder  {exprPos :: Pos}
                | ETyped    {exprPos :: Pos, exprExpr :: e, exprTSpec :: Type}
                | ERelPred  {exprPos :: Pos, exprRel :: String, exprArgs :: [e]}

instance Eq e => Eq (ExprNode e) where
    (==) (EVar _ v1)              (EVar _ v2)                = v1 == v2
    (==) (EPacket _)              (EPacket _)                = True
    (==) (EApply _ f1 as1)        (EApply _ f2 as2)          = f1 == f2 && as1 == as2
    (==) (EField _ s1 f1)         (EField _ s2 f2)           = s1 == s2 && f1 == f2
    (==) (ELocation _ r1 k1)      (ELocation _ r2 k2)        = r1 == r2 && k1 == k2
    (==) (EBool _ b1)             (EBool _ b2)               = b1 == b2
    (==) (EInt _ i1)              (EInt _ i2)                = i1 == i2
    (==) (EString _ s1)           (EString _ s2)             = s1 == s2
    (==) (EBit _ w1 i1)           (EBit _ w2 i2)             = w1 == w2 && i1 == i2
    (==) (EStruct _ c1 fs1)       (EStruct _ c2 fs2)         = c1 == c2 && fs1 == fs2
    (==) (ETuple _ fs1)           (ETuple _ fs2)             = fs1 == fs2
    (==) (ESlice _ e1 h1 l1)      (ESlice _ e2 h2 l2)        = e1 == e2 && h1 == h2 && l1 == l2
    (==) (EMatch _ e1 cs1)        (EMatch _ e2 cs2)          = e1 == e2 && cs1 == cs2
    (==) (EVarDecl _ v1)          (EVarDecl _ v2)            = v1 == v2
    (==) (ESeq _ l1 r1)           (ESeq _ l2 r2)             = l1 == l2 && r1 == r2
    (==) (EPar _ l1 r1)           (EPar _ l2 r2)             = l1 == l2 && r1 == r2
    (==) (EITE _ i1 t1 e1)        (EITE _ i2 t2 e2)          = i1 == i2 && t1 == t2 && e1 == e2
    (==) (EDrop _)                (EDrop _)                  = True
    (==) (ESet _ l1 r1)           (ESet _ l2 r2)             = l1 == l2 && r1 == r2
    (==) (ESend _ d1)             (ESend _ d2)               = d1 == d2
    (==) (EBinOp _ o1 l1 r1)      (EBinOp _ o2 l2 r2)        = o1 == o2 && l1 == l2 && r1 == r2
    (==) (EUnOp _ o1 e1)          (EUnOp _ o2 e2)            = o1 == o2 && e1 == e2
    (==) (EFor  _ v1 t1 c1 b1)    (EFor  _ v2 t2 c2 b2)      = v1 == v2 && t1 == t2 && c1 == c2 && b1 == b2
    (==) (EFork _ v1 t1 c1 b1)    (EFork _ v2 t2 c2 b2)      = v1 == v2 && t1 == t2 && c1 == c2 && b1 == b2
    (==) (EWith _ v1 t1 c1 b1 d1) (EWith _ v2 t2 c2 b2 d2)   = v1 == v2 && t1 == t2 && c1 == c2 && b1 == b2 && d1 == d2
    (==) (EAny _ v1 t1 c1 b1 d1)  (EAny _ v2 t2 c2 b2 d2)    = v1 == v2 && t1 == t2 && c1 == c2 && b1 == b2 && d1 == d2
    (==) (EPHolder _)             (EPHolder _)               = True
    (==) (ETyped _ e1 t1)         (ETyped _ e2 t2)           = e1 == e2 && t1 == t2
    (==) (ERelPred _ r1 as1)      (ERelPred _ r2 as2)        = r1 == r2 && as1 == as2
    (==) _                        _                          = False

instance WithPos (ExprNode e) where
    pos = exprPos
    atPos e p = e{exprPos = p}

instance PP e => PP (ExprNode e) where
    pp (EVar _ v)          = pp v
    pp (EPacket _)         = pp pktVar
    pp (EApply _ f as)     = pp f <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EField _ s f)      = pp s <> char '.' <> pp f
    pp (ELocation _ r k)   = pp r <> (brackets $ pp k)
    pp (EBool _ True)      = pp "true"
    pp (EBool _ False)     = pp "false"
    pp (EInt _ v)          = pp v
    pp (EString _ s)       = pp s
    pp (EBit _ w v)        = pp w <> pp "'d" <> pp v
    pp (EStruct _ s fs)    = pp s <> (braces $ hsep $ punctuate comma $ map pp fs)
    pp (ETuple _ fs)       = parens $ hsep $ punctuate comma $ map pp fs
    pp (ESlice _ e h l)    = pp e <> (brackets $ pp h <> colon <> pp l)
    pp (EMatch _ e cs)     = pp "match" <+> pp e <+> (braces $ vcat 
                                                       $ punctuate comma 
                                                       $ (map (\(c,v) -> pp c <> colon <+> pp v) cs))
    pp (EVarDecl _ v)      = pp "var" <+> pp v
    pp (ESeq _ l r)        = (pp l <> semi) $$ pp r
    pp (EPar _ l r)        = (pp l <> pp "|" ) $$ pp r
    pp (EITE _ c t me)     = (pp "if" <+> pp c <+> lbrace)
                             $$
                             (nest' $ pp t)
                             $$
                             rbrace <+> (maybe empty (\e -> (pp "else" <+> lbrace) $$ (nest' $ pp e) $$ rbrace) me)
    pp (EDrop _)           = pp "drop"
    pp (ESet _ l r)        = pp l <+> pp "=" <+> pp r
    pp (ESend  _ e)        = pp "send" <+> pp e
    pp (EBinOp _ op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp _ op e)      = parens $ pp op <+> pp e
    pp (EFor  _ v t c b)   = (pp "for"  <+> (parens $ pp v <+> pp "in" <+> pp t <+> pp "|" <+> pp c)) $$ (nest' $ pp b)
    pp (EFork _ v t c b)   = (pp "fork" <+> (parens $ pp v <+> pp "in" <+> pp t <+> pp "|" <+> pp c)) $$ (nest' $ pp b)
    pp (EWith _ v t c b d) = (pp "the" <+> (parens $ pp v <+> pp "in" <+> pp t <+> pp "|" <+> pp c)) 
                             $$ (nest' $ pp b)
                             $$ (maybe empty (\e -> pp "default" <+> pp e)  d)
    pp (EAny _ v t c b d)  = (pp "any" <+> (parens $ pp v <+> pp "in" <+> pp t <+> pp "|" <+> pp c)) 
                             $$ (nest' $ pp b)
                             $$ (maybe empty (\e -> pp "default" <+> pp e)  d)
    pp (EPHolder _)        = pp "_"
    pp (ETyped _ e t)      = parens $ pp e <> pp ":" <+> pp t
    pp (ERelPred _ rel as) = pp rel <> (parens $ hsep $ punctuate comma $ map pp as)

instance PP e => Show (ExprNode e) where
    show = render . pp

type ENode = ExprNode Expr

newtype Expr = E (ExprNode Expr)
enode :: Expr -> ExprNode Expr
enode (E n) = n

instance Eq Expr where
    (==) (E e1) (E e2) = e1 == e2

instance PP Expr where
    pp (E n) = pp n

instance Show Expr where
    show (E n) = show n

instance WithPos Expr where
    pos (E n) = pos n
    atPos (E n) p = E $ atPos n p

eVar v              = E $ EVar      nopos v
ePacket             = E $ EPacket   nopos
eApply f as         = E $ EApply    nopos f as
eField e f          = E $ EField    nopos e f
eLocation r k       = E $ ELocation nopos r k
eBool b             = E $ EBool     nopos b
eTrue               = eBool True
eFalse              = eBool False
eInt i              = E $ EInt      nopos i
eString s           = E $ EString   nopos s
eBit w v            = E $ EBit      nopos w v
eStruct c as        = E $ EStruct   nopos c as
eTuple [a]          = a
eTuple as           = E $ ETuple    nopos as
eSlice e h l        = E $ ESlice    nopos e h l
eMatch e cs         = E $ EMatch    nopos e cs
eVarDecl v          = E $ EVarDecl  nopos v
eSeq l r            = E $ ESeq      nopos l r
ePar l r            = E $ EPar      nopos l r
eITE i t e          = E $ EITE      nopos i t e
eDrop               = E $ EDrop     nopos
eSet l r            = E $ ESet      nopos l r
eSend e             = E $ ESend     nopos e
eBinOp op l r       = E $ EBinOp    nopos op l r
eUnOp op e          = E $ EUnOp     nopos op e
eNot e              = eUnOp Not e
eFork v t c b       = E $ EFork     nopos v t c b
eFor  v t c b       = E $ EFor      nopos v t c b
eWith v t c b d     = E $ EWith     nopos v t c b d
eAny v t c b d      = E $ EAny      nopos v t c b d
ePHolder            = E $ EPHolder  nopos
eTyped e t          = E $ ETyped    nopos e t
eRelPred rel as     = E $ ERelPred  nopos rel as

exprIsRelPred :: Expr -> Bool
exprIsRelPred (E (ERelPred{})) = True
exprIsRelPred _                = False

conj :: [Expr] -> Expr
conj = conj' . filter (/= eTrue)

conj' :: [Expr] -> Expr
conj' []     = eTrue
conj' [e]    = e
conj' (e:es) = eBinOp And e (conj' es)

disj :: [Expr] -> Expr
disj = disj' . filter (/= eFalse)

disj' :: [Expr] -> Expr
disj' []     = eFalse
disj' [e]    = e
disj' (e:es) = eBinOp Or e (disj' es)

exprSequence :: [Expr] -> Expr
exprSequence []     = error "exprSequence []" 
exprSequence [e]    = e
exprSequence (e:es) = eSeq e (exprSequence es)

data ECtx = CtxRefine
          | CtxRole      {ctxRole::Role}
          | CtxRoleGuard {ctxRole::Role}
          | CtxPktGuard  {ctxRole::Role}
          | CtxFunc      {ctxFunc::Function, ctxPar::ECtx}
          | CtxAssume    {ctxAssume::Assume}
          | CtxRelKey    {ctxRel::Relation}
          | CtxRelForeign{ctxRel::Relation, ctxConstr::Constraint}
          | CtxCheck     {ctxRel::Relation}
          | CtxRuleL     {ctxRel::Relation, ctxRule::Rule, ctxIdx::Int}
          | CtxRuleR     {ctxRel::Relation, ctxRule::Rule}
          | CtxApply     {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          | CtxField     {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxLocation  {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxStruct    {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          | CtxTuple     {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          | CtxSlice     {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxMatchExpr {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxMatchPat  {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          | CtxMatchVal  {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          | CtxSeq1      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxSeq2      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxPar1      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxPar2      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxITEIf     {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxITEThen   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxITEElse   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxSetL      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxSetR      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxSend      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxBinOpL    {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxBinOpR    {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxUnOp      {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxForCond   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxForBody   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxForkCond  {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxForkBody  {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxWithCond  {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxWithBody  {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxWithDef   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxAnyCond   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxAnyBody   {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxAnyDef    {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxTyped     {ctxParExpr::ENode, ctxPar::ECtx}
          | CtxRelPred   {ctxParExpr::ENode, ctxPar::ECtx, ctxIdx::Int}
          deriving(Show)

ctxParent :: ECtx -> ECtx
ctxParent (CtxRole _)         = CtxRefine     
ctxParent (CtxRoleGuard _)    = CtxRefine     
ctxParent (CtxPktGuard _)     = CtxRefine     
ctxParent (CtxAssume _)       = CtxRefine
ctxParent (CtxRelKey _)       = CtxRefine
ctxParent (CtxRelForeign _ _) = CtxRefine
ctxParent (CtxCheck _)        = CtxRefine
ctxParent (CtxRuleL _ _ _)    = CtxRefine
ctxParent (CtxRuleR _ _)      = CtxRefine
ctxParent ctx                 = ctxPar ctx

ctxAncestors :: ECtx -> [ECtx]
ctxAncestors CtxRefine = [CtxRefine]
ctxAncestors ctx       = ctx : (ctxAncestors $ ctxParent ctx)

ctxIsRelPred :: ECtx -> Bool
ctxIsRelPred CtxRelPred{} = True
ctxIsRelPred _            = False

ctxInRelPred :: ECtx -> Bool
ctxInRelPred ctx = any ctxIsRelPred $ ctxAncestors ctx

ctxIsRuleL :: ECtx -> Bool
ctxIsRuleL CtxRuleL{} = True
ctxIsRuleL _          = False

ctxInRuleL :: ECtx -> Bool
ctxInRuleL ctx = any ctxIsRuleL $ ctxAncestors ctx

ctxIsMatchPat :: ECtx -> Bool
ctxIsMatchPat CtxMatchPat{} = True
ctxIsMatchPat _             = False

ctxInMatchPat :: ECtx -> Bool
ctxInMatchPat ctx = isJust $ ctxInMatchPat' ctx

ctxInMatchPat' :: ECtx -> Maybe ECtx
ctxInMatchPat' ctx = find ctxIsMatchPat $ ctxAncestors ctx

ctxIsSetL :: ECtx -> Bool
ctxIsSetL CtxSetL{} = True
ctxIsSetL _         = False

ctxInSetL :: ECtx -> Bool
ctxInSetL ctx = any ctxIsSetL $ ctxAncestors ctx

ctxIsSeq1 :: ECtx -> Bool
ctxIsSeq1 CtxSeq1{} = True
ctxIsSeq1 _         = False

ctxInSeq1 :: ECtx -> Bool
ctxInSeq1 ctx = any ctxIsSeq1 $ ctxAncestors ctx

ctxIsRole :: ECtx -> Bool
ctxIsRole CtxRole{} = True
ctxIsRole _         = False

ctxInRole :: ECtx -> Bool
ctxInRole ctx = any ctxIsRole $ ctxAncestors ctx

ctxIsTyped :: ECtx -> Bool
ctxIsTyped CtxTyped{} = True
ctxIsTyped _          = False
