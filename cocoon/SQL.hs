{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

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

{-# LANGUAGE RecordWildCards, LambdaCase, ScopedTypeVariables, ImplicitParams #-}

-- Cocoon's SQL backend

module SQL (sqlMaxIntWidth, mkSchema) where

import Data.List
import Data.List.Utils
import Data.Bits
import Data.Maybe
import Data.Char
import Data.Tuple.Select
import Text.PrettyPrint
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Query.DFS as G

import Name
import Pos
import PP
import Util
import Syntax
import Expr
import Type
import NS
import Relation

sqlMaxIntWidth :: Int
sqlMaxIntWidth = 63

tag = "tag$"
matchvar = "match$"

commaSep = hsep . punctuate comma . filter (not . isEmpty)
vcommaSep = vcat . punctuate comma . filter (not . isEmpty)

andSep = andSep' . filter (not . isEmpty)

andSep' []  = empty
andSep' [x] = x
andSep' xs  = parens $ hsep $ punctuate (pp " and") xs

vandSep = vandSep' . filter (not . isEmpty)

vandSep' []  = empty
vandSep' [x] = x
vandSep' xs  = parens $ vcat $ punctuate (pp " and") xs

-- TODO
-- Special tables
-- * Connection tracker
-- (* ACL )
-- primary key in a view
    -- has primary key - OK
    -- otherwise, pick a unique key that's always present
    -- otherwise, use a combination of all fields

-- TODO: for purely local state (only read and written by a single switch),
-- store the table on switche's local controller
mkSchema :: String -> Refine -> Doc
mkSchema dbname r@Refine{..} = let ?r = r in
                               vcat $ intersperse (pp "") $ createdb : 
                                                            (map mkTypeDef tdefs) ++ 
                                                            (map (mk . getRelation r) rels) ++
                                                            (map mkFun funs)
                                                            
    where rels = reverse $ G.topsort' $ relGraph r
          createdb = pp "drop database if exists" <+> pp dbname <> semi
                     $$
                     pp "create database" <+> pp dbname <> semi
                     $$
                     pp "\\c" <+> pp dbname
          mk rel = case relDef rel of
                        Nothing -> mkRel rel
                        _       -> mkView rel
          funs = map (getFunc r) $ nub $ concatMap (relFuncsRec r) refineRels 
          types = nub $ concatMap (relTypes r) refineRels
          types' = nub $ map (typ' r) $ reverse $ G.topsort' $ typeGraph r types
          tdefs = mapMaybe (\t -> case t of
                                       TStruct{..} -> Just $ structTypeDef r t
                                       _           -> Nothing) types'

mkTypeDef :: (?r::Refine) => TypeDef -> Doc
mkTypeDef (TypeDef _ n (Just (TStruct _ cs))) = 
    pp "create type" <+> pp n <+> pp "as (" $$
    (nest' $ vcommaSep $ t ++ (map (\f -> pp (name f) <+> (mkType $ typ f)) $ structFields cs)) $$
    pp ");"
    where needtag = length cs > 1
          t = (if' needtag [pp tag <+> (mkType $ tagType cs)] [])
mkTypeDef t = error $ "SQL.mkTypeDef " ++ show t

mkFun :: (?r::Refine) => Function -> Doc
mkFun f@Function{..} = 
            pp "create function" <+> (pp $ name f) <+> (parens $ commaSep $ map (\a -> (pp $ name a) <+> mkType (typ a)) funcArgs) <+> 
            pp "returns" <+> mkType funcType <+> pp "as $$" $$
            pp "begin" $$
            (nest' $ mkExpr (CtxFunc f CtxRefine) $ fromJust funcDef) $$
            pp "end;" $$  
            pp "$$ language plpgsql" <> semi

mkExpr :: (?r::Refine) => ECtx -> Expr -> Doc
mkExpr ctx e = mkNormalizedExprF ctx e'
    where
    e' = evalState (do e1 <- expr2Statement ?r ctx e
                       e2 <- exprSplitLHS ?r ctx e1
                       return $ exprSplitVDecl ?r ctx e2) 0

mkRel :: (?r::Refine) => Relation -> Doc
mkRel rel@Relation{..} = (vcat $ map sel1 cons) $$
                         pp "create table" <+> pp relName <+> pp "("
                         $$
                         (nest' $ vcommaSep $ cols ++ map sel2 cons)
                         $$
                         pp ");"
                         $$
                         (vcat $ map sel3 cons)
    where
    -- Primary table
    cols = map mkColumn relArgs
    cons = mapIdx (mkConstraint rel) relConstraints
    -- Delta table
    -- Primary-delta synchronization triggers

mkView :: (?r::Refine) => Relation -> Doc
mkView rel@Relation{..} = (vcat $ map sel1 cons) $$
                          pp "create" <+> (if' isrec (pp "recursive") empty) <+> pp "view" <+> pp relName <+> 
                          (parens $ commaSep $ concatMap (\a -> map (colName . sel1) 
                                                                $ e2cols (typ a) $ eVar $ name a) $ relArgs) <+> pp "as"
                          $$
                          (vcat $ intersperse (pp "UNION") $ map (nest' . mkRule rel) $ simprules ++ recrules) <> semi
    where
    (recrules, simprules) = partition (ruleIsRecursive rel) $ fromJust relDef
    isrec = not $ null recrules
    cons = mapIdx (mkConstraint rel) relConstraints
    
    -- Primary table
    -- Delta table
    -- rel' = 
    -- Primary-delta synchronization triggers

mkRule :: (?r::Refine) => Relation -> Rule -> Doc
mkRule rel rule@Rule{..} = 
    (pp "select distinct") $$
    (nest' $ vcommaSep $ concatMap (uncurry mkarg) $ zip (relArgs rel) ruleLHS) $$
    (pp "from") $$ 
    (nest' $ commaSep $ map (\(p, n) -> (pp $ exprRel p) <+> pp n) prednames) $$
    (pp "where") $$
    (nest' $ vandSep [predconstr, eqconstr, arithconstr])
  where 
    (preds, conds) = partition exprIsRelPred ruleRHS
    prednames :: [(ENode, String)]
    prednames = evalState (mapM (\(E p) -> do (i::Int) <- (liftM $ maybe 0 (+1)) $ gets (M.lookup (exprRel p))
                                              modify $ M.insert (exprRel p) i
                                              return (p, exprRel p ++ show i)) preds) M.empty
    vars = ctxAllVars ?r (CtxRuleR rel rule)
    -- Variable to column mapping
    varcols :: [(Field, [Expr])]
    varcols = zip vars
              $ map (\v -> concatMap (\(p, pname) -> map (ctx2Field (eVar pname) . snd) 
                                                     $ filter ((name v ==) . fst)
                                                     $ exprVars (CtxRuleR rel rule) $ E p) prednames)
                    vars
    -- LHS arguments
    mkarg arg val = let cols = field2cols rel (eVar $ name arg)
                        vals = map sel1 $ e2cols (fieldType arg) $ subst val
                    in map (\(v, c) -> colName v <+> pp "as" <+> colName c) $ zip vals cols
    -- collect (constructor) constraints from individual relations
    predconstr = mkNormalizedExprV (CtxRuleR rel rule) $ conj 
                 $ map (\(ERelPred _ rname as, tname) -> 
                        let Relation{..} = getRelation ?r rname in
                        conj $ map (\(f,a) -> pattern2Constr (eField (eVar tname) $ name f) (typ f) a) 
                             $ zip relArgs as) 
                       prednames
    -- collect non-predicate constraints (conds)
    arithconstr = mkNormalizedExprV (CtxRuleR rel rule) $ conj $ map subst conds
    -- collect equality constraints
    eqconstr = andSep
               $ map (\(f, e:es) -> let ecols = e2cols (typ f) e in
                                    andSep $ map (\e' -> let ecols' = e2cols (typ f) e' in
                                                         andSep $ map (\(c1,c2) -> mkSqlCol c1 <+> pp "=" <+> mkSqlCol c2)
                                                                      $ zip ecols ecols') es) 
                     varcols
    -- substitute variable names with matching column names in expression
    subst e = exprFold subst' e
    subst' (EVar _ v) = head $ snd $ fromJust $ find ((== v) . name . fst) varcols
    subst' e          = E e


--- r, m, Cons1{_,_,Cons2{x,_}} ===> m.f1.f2
ctx2Field :: (?r::Refine) => Expr -> ECtx -> Expr
ctx2Field pref CtxMatchPat{}                         = pref
ctx2Field pref (CtxTyped _ pctx)                     = ctx2Field pref pctx
ctx2Field pref (CtxRelPred (ERelPred _ rname _) _ i) = let rel' = getRelation ?r rname in
                                                       eField pref $ name $ relArgs rel' !! i
ctx2Field pref (CtxStruct (EStruct _ c _) pctx i)    = let cons = getConstructor ?r c in
                                                       eField (ctx2Field pref pctx) $ name $ consArgs cons !! i
ctx2Field pref ctx                                   = error $ "SQL.ctx2Field " ++ show pref ++ " " ++ show ctx


pattern2Constr :: (?r::Refine) => Expr -> Type -> Expr -> Expr
pattern2Constr pref t (E EStruct{..}) = conj 
                                         $ (if' (length cs > 1) [eBinOp Eq (eField pref tag) (tagVal cs c)] []) ++
                                           (map (\(f,a) -> pattern2Constr (eField pref $ name f) (typ f) a) $ zip fs exprFields)
    where TStruct _ cs = typ' ?r t
          Constructor _ c fs = getConstructor ?r exprConstructor
pattern2Constr _    _ _               = eBool True

-- Only works for expressions whose variables are known to be non-NULL
-- (i.e., don't need to be coalesced)

-- view context
mkNormalizedExprV :: (?r::Refine) => ECtx -> Expr -> Doc
mkNormalizedExprV ctx = let ?sep = pp "$"
                        in mkNormalizedExpr ctx

-- function context
mkNormalizedExprF :: (?r::Refine) => ECtx -> Expr -> Doc
mkNormalizedExprF ctx = let ?sep = pp "."
                        in mkNormalizedExpr ctx

mkNormalizedExpr :: (?r::Refine, ?sep::Doc) => ECtx -> Expr -> Doc
mkNormalizedExpr ctx e = snd $ exprFoldCtx (\ctx' en -> let d =  mkNormalizedExprRet ctx' en
                                                            e' = E $ exprMap fst en
                                                        in (e', d)) ctx e

mkNormalizedExprRet :: (?r::Refine, ?sep::Doc) => ECtx -> ExprNode (Expr, Doc) -> Doc
mkNormalizedExprRet ctx e | ctxMustReturn ctx && not (exprIsStatement $ enode ex)  = pp "return" <+> e' <> semi
                          | ctxExpectsStat ctx && not (exprIsStatement $ enode ex) = pp "perform" <+> e' <> semi
                          | otherwise                                              = e'
    where e' = mkNormalizedExpr' ctx e
          ex = E $ exprMap fst e

mkNormalizedExpr' :: (?r::Refine, ?sep::Doc) => ECtx -> ExprNode (Expr, Doc) -> Doc
mkNormalizedExpr' _    (EVar _ v)                    = pp v
mkNormalizedExpr' _    (EField _ (_, s') f)          = s' <> (if' (isUpper s0 && notElem '.' ss) (pp ".") ?sep) <> pp f
    where s0:ss = render s'
mkNormalizedExpr' _    (EBool _ b)                   = mkVal $ enode $ eBool b
mkNormalizedExpr' _    (EString _ s)                 = mkVal $ enode $ eString s
mkNormalizedExpr' _    (EBit _ w v)                  = mkVal $ enode $ eBit w v
mkNormalizedExpr' _    (EUnOp _ Not (_,e'))          = parens $ pp "not" <+> e'
mkNormalizedExpr' _    (EBinOp _ op (_,l') (_, r'))  = parens $ 
    case op of
         Eq     -> l' <+> pp "="   <+> r'
         Neq    -> l' <+> pp "<>"  <+> r'
         Lt     -> l' <+> pp "<"   <+> r'
         Gt     -> l' <+> pp ">"   <+> r'
         Lte    -> l' <+> pp "<="  <+> r'
         Gte    -> l' <+> pp ">="  <+> r'
         And    -> l' <+> pp "and" <+> r'
         Or     -> l' <+> pp "or"  <+> r'
         Impl   -> parens (pp "not" <+> l') <+> pp "or"  <+> r'
         Plus   -> l' <+> pp "+"   <+> r'
         Minus  -> l' <+> pp "-"   <+> r'
         Mod    -> l' <+> pp "%"   <+> r'
         ShiftR -> l' <+> pp ">>"  <+> r'
         ShiftL -> l' <+> pp "<<"  <+> r'
         _      -> error $ "SQL.mkNormalizedExpr EBinOp " ++ show op
mkNormalizedExpr' _    (ETyped _  (_, e') _)         = e'
mkNormalizedExpr' _    (EApply _ f as)               = pp f <+> (parens $ commaSep $ map snd as)
mkNormalizedExpr' _    (EStruct _ c fs)              = 
    let TStruct _ cs = fromJust $ tdefType $ consType ?r c
        Constructor _ _ as = getConstructor ?r c
        needtag = length cs > 1 in
    parens $ commaSep
    $ (if' needtag (mkVal $ enode $ tagVal cs c) empty) :
      (map (\f -> maybe (pp "NULL") (snd . (fs !!)) $ elemIndex f as) 
           $ structFields cs)
mkNormalizedExpr' ctx e@(EMatch _ (m,m') cs)         = 
    match $$
    (nest' $ pp "case" $$
             (nest' $ vcat $ mapIdx mkCase cs) $$
             pp "end case;") $$
    pp "end;"
    where ex = exprMap fst e
          mtype = exprType ?r (CtxMatchExpr ex ctx) m
          match = pp "declare" $$ (nest' $ pp matchvar <+> mkType mtype <> semi) $$
                  pp "begin" $$ (nest' $ pp matchvar <+> pp ":=" <+> m' <> semi)
          mkCase ((pat, _), (_, v')) i = 
            pp "when" <+> mkNormalizedExpr CtxRefine cond <+> pp "then" $$
            (if' (null decls) 
                 (pp "begin")
                 (pp "declare" $$ (nest' $ vcat decls) $$ pp "begin" $$ (nest' $ vcat asns))) $$
            nest' v' $$ pp "end" <> semi
            where cond  = pattern2Constr (eVar matchvar) mtype pat
                  (decls, asns) = unzip $
                          map (\(x, ctx') -> (pp x <+> mkType (fromJust $ ctxExpectType ?r ctx') <> semi, 
                                              pp x <+> pp ":=" <+> (mkNormalizedExpr CtxRefine $ ctx2Field (eVar matchvar) ctx') <> semi)) 
                              $ exprVarDecls (CtxMatchPat ex ctx i) pat
mkNormalizedExpr' ctx   (EVarDecl _ v)     = pp "declare" $$ (nest' $ pp v <+> (mkType $ fromJust $ ctxExpectType ?r ctx)) <> semi
mkNormalizedExpr' _     (EPHolder _)       = empty
mkNormalizedExpr' _     (ESeq _ (_,e1') (_,e2'))     = e1' $$ pp "begin" $$ nest' e2' $$ pp "end" <> semi
mkNormalizedExpr' _     (EITE _ (_,c') (_,t') me)    = pp "if" <+> c' <+> pp "then" $$
                                                       (nest' t') $$
                                                       (maybe empty ((pp "else" $$) . nest' . snd) me)
mkNormalizedExpr' _     (ESet _ (_,l') (_,r'))       = l' <+> pp ":=" <+> r' <> semi
mkNormalizedExpr' _     e                            = error $ "SQL.mkNormalizedExpr " ++ (render $ pp $ exprMap fst e)

mkColumn :: (?r::Refine) => Field -> Doc
mkColumn f = mkColumn' (fieldType f) $ eVar $ name f

mkColumn' :: (?r::Refine) => Type -> Expr -> Doc
mkColumn' t e = vcat $ punctuate comma 
                $ map (\(e', t', _) -> colName e' <+> mkType t')
                $ e2cols t e
    
colName :: Expr -> Doc
colName e = let (tname, rest) = span (/= '.') $ render $ pp e in
            if null rest 
               then pp tname
               else if isUpper $ head tname 
                       then pp $ tname ++ "." ++ (replace "." "$" $ tail rest)
                       else pp $ tname ++ "$" ++ (replace "." "$" $ tail rest)

field2cols :: (?r::Refine) => Relation -> Expr -> [Expr]
field2cols rel e = map sel1 $ e2cols (exprType ?r (CtxRelKey rel) e) e

e2cols :: (?r::Refine) => Type -> Expr -> [(Expr, Type, Bool)]
e2cols t e = e2cols' t $ Just e

e2cols' :: (?r::Refine) => Type -> Maybe Expr -> [(Expr, Type, Bool)]
e2cols' t (Just (E (ETyped _ e _))) = e2cols' t $ Just e
e2cols' t me = 
    case typ' ?r t of
         TStruct _ cs  -> let needtag = length cs > 1 in
                          case me of 
                               Nothing ->                   (if' needtag [(defVal $ tagType cs, tagType cs, False)] []) ++
                                                            (concatMap (\f -> e2cols' (typ f) Nothing) $ structFields cs)
                               Just (E (EStruct _ c fs)) -> let Constructor _ _ as = getConstructor ?r c in
                                                                (if' needtag [(tagVal cs c, tagType cs, False)] []) ++ 
                                                                (concatMap (\f -> e2cols' (typ f) $ fmap (fs !!) $ elemIndex f as) 
                                                                           $ structFields cs)
                               Just e                    -> (if' needtag [(eField e tag, tagType cs, False)] []) ++
                                                            ((if' needtag (map (\(e', t', _) -> (e', t', True))) id)
                                                             $ concatMap (\f -> e2cols' (typ f) $ Just $ eField e $ name f)
                                                             $ structFields cs)
         _             -> maybe [(defVal t, t, False)] (\e -> [(e, t, False)]) me

mkType :: (?r::Refine) => Type -> Doc
mkType t = mkType' (typ' ?r t)

mkType' :: (?r::Refine) => Type -> Doc
mkType' t@TStruct{}              = pp $ name $ structTypeDef ?r t
mkType'   TBool{}                = pp "boolean"
mkType'   TString{}              = pp "text"
mkType'   (TBit _ w) | w < 32    = pp "int"
                     | w < 64    = pp "bigint"
                     | otherwise = pp "bit" <> (parens $ pp w)
mkType' t                        = error $ "SQL.mkType " ++ show t

tagType :: [Constructor] -> Type
tagType cs = tBit $ bitWidth $ length cs - 1

tagVal :: [Constructor] -> String -> Expr
tagVal cs c = eBit (typeWidth $ tagType cs) $ fromIntegral $ fromJust $ findIndex ((== c) . name) cs

defVal :: Type -> Expr
defVal (TStruct _ cs) = defVal $ tagType cs
defVal (TBool _)      = eBool False
defVal (TString _)    = eString ""
defVal (TBit _ w)     = eBit w 0
defVal t              = error $ "SQL.defVal " ++ show t

mkVal :: (PP a) => ExprNode a -> Doc
mkVal (EBool _ True)  = pp "true"
mkVal (EBool _ False) = pp "false"
mkVal (EString _ str) = pp $ show str
mkVal (EBit _ w v) | w < 64    = pp v
                   | otherwise = pp $ "B'" ++ (map ((\b -> if' b '1' '0') . testBit v) [0..w-1]) ++ "'"
mkVal e               = error $ "SQL.mkVal " ++ (render $ pp e)

mkConstraint :: (?r::Refine) => Relation -> Constraint -> Int -> (Doc, Doc, Doc)
mkConstraint rel (PrimaryKey _ fs) _           = 
    (empty, pp "primary key" <+> (parens $ commaSep $ concatMap (map colName . field2cols rel) fs), empty)
mkConstraint rel (ForeignKey _ fs rname fs') _ = 
    ( empty
    , let rel' = getRelation ?r rname in
      pp "foreign key" <+> 
      (parens $ commaSep $ concatMap (map colName . field2cols rel) fs) <+>
      pp "references" <+> 
      (pp rname <+> (parens $ commaSep $ concatMap (map colName . field2cols rel') fs'))
    , empty)
mkConstraint rel (Unique _ fs) _ = 
    ( empty,
      empty,
      pp "create unique index on" <+> (pp $ name rel) <+>
      (parens $ commaSep
       $ map mkSqlCol
       $ concatMap (\f -> e2cols (exprType ?r (CtxRelKey rel) f) f) fs) <> semi)
mkConstraint rel (Check _ cond) i              = (mkFun func, pp "check" <> parens call, empty)
    where fname    = "check" ++ name rel ++ "$" ++ show i
          fields   = exprVars (CtxCheck rel) cond
          fargs    = map (\(v, ctx) -> Field nopos v (exprType ?r ctx (eVar v))) fields
          func     = Function nopos True fname fargs tBool (Just cond)
          callargs = map (gather . (\f -> (eVar $ name f, typ f))) fargs
          gather (e, t) = case typ' ?r t of
                               TStruct _ cs -> parens $ commaSep 
                                               $ map (\f -> gather (eField e $ name f, typ f)) 
                                               $ (if' (length cs > 1) [Field nopos tag $ tagType cs] []) ++ (structFields cs)
                               _            -> mkNormalizedExprV (CtxCheck rel) e
          call     = pp fname <> (parens $ commaSep callargs)


mkSqlCol :: (Expr, Type, Bool) -> Doc
mkSqlCol (e, _, False) = colName e
mkSqlCol (e, t, True)  = pp "coalesce" <> (parens $ colName e <> comma <+> (mkVal $ enode $ defVal t))

