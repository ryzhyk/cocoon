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

{-# LANGUAGE RecordWildCards, LambdaCase, ScopedTypeVariables #-}

-- Cocoon's SQL backend

module SQL (sqlMaxIntWidth, mkSchema) where

import Data.List
import Data.List.Utils
import Data.Bits
import Data.Maybe
import Data.Tuple.Select
import Text.PrettyPrint
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Query.DFS as G

import Name
import PP
import Util
import Syntax
import Expr
import Type
import NS
import Relation

sqlMaxIntWidth :: Int
sqlMaxIntWidth = 63

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



-- Special tables
-- * Connection tracker
-- (* ACL )
-- primary key in a view
    -- has primary key - OK
    -- otherwise, pick a unique key that's always present
    -- otherwise, use a combination of all fields

-- Where are relations stored

-- TODO: for purely local state (only read and written by a single switch),
-- store the table on switche's local controller
mkSchema :: String -> Refine -> Doc
mkSchema dbname r@Refine{..} = createdb $$ (vcat $ map mk $ map (getRelation r) ordered)
    where ordered = reverse $ G.topsort' $ relGraph r
          createdb = pp "drop database if exists" <+> pp dbname <> semi
                     $$
                     pp "create database" <+> pp dbname <> semi
                     $$
                     pp "\\c" <+> pp dbname
          mk rel = case relDef rel of
                        Nothing -> mkRel r rel
                        _       -> mkView r rel
          -- funs = map (mkFun r) $ -- functions used in constraints

mkRel :: Refine -> Relation -> Doc
mkRel r rel@Relation{..} = pp "create table" <+> pp relName <+> pp "("
                           $$
                           (nest' $ vcommaSep $ cols ++ map fst cons)
                           $$
                           pp ");"
                           $$
                           (vcat $ map snd cons)
    where
    -- Primary table
    cols = map (mkColumn r) relArgs
    cons = map (mkConstraint r rel) relConstraints
    -- Delta table
    -- rel' = 
    -- Primary-delta synchronization triggers

mkView :: Refine -> Relation -> Doc
mkView r rel@Relation{..} = pp "create" <+> (if' isrec (pp "recursive") empty) <+> pp "view" <+> pp relName <+> 
                            (parens $ commaSep $ concatMap (\a -> map (colName . sel1) 
                                                                  $ e2cols r (typ a) $ eVar $ name a) $ relArgs) <+> pp "as"
                            $$
                            (vcat $ intersperse (pp "UNION") $ map (nest' . mkRule r rel) $ simprules ++ recrules) <> semi
    where
    (recrules, simprules) = partition (ruleIsRecursive rel) $ fromJust relDef
    isrec = not $ null recrules
    
    -- Primary table
    -- Delta table
    -- rel' = 
    -- Primary-delta synchronization triggers
{-
CREATE [RECURSIVE] VIEW reporting_line (employee_id, subordinates) AS 
SELECT
 a.employee_id as arg1,
 b.xxx as arg2,
FROM
    rel1 a, rel2 b
WHERE
 manager_id IS NULL
UNION ALL
 SELECT
 e.employee_id,
 (
 rl.subordinates || ' > ' || e.full_name
 ) AS subordinates
 FROM
 employees e
 INNER JOIN reporting_line rl ON e.manager_id = rl.employee_id;
-}


mkRule :: Refine -> Relation -> Rule -> Doc
mkRule r rel rule@Rule{..} = 
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
    vars = ctxAllVars r (CtxRuleR rel rule)
    -- Variable to column mapping
    varcols :: [(Field, [Expr])]
    varcols = zip vars
              $ map (\v -> concatMap (\(p, pname) -> map (ctx2col pname . snd) 
                                                     $ filter ((name v ==) . fst)
                                                     $ exprVars (CtxRuleR rel rule) $ E p) prednames)
                    vars
    ctx2col pname (CtxRelPred (ERelPred _ rname _) _ i) = let rel' = getRelation r rname in
                                                          eField (eVar pname) $ name $ relArgs rel' !! i
    ctx2col pname (CtxStruct (EStruct _ c _) pctx i) = let cons = getConstructor r c in
                                                       eField (ctx2col pname pctx) $ name $ consArgs cons !! i
    ctx2col _     ctx                                = error $ "SQL.mkRule.ctx2col " ++ show ctx

    -- LHS arguments
    mkarg arg val = let cols = field2cols r rel (eVar $ name arg)
                        vals = map sel1 $ e2cols r (fieldType arg) $ subst val
                    in map (\(v, c) -> fcolName v <+> pp "as" <+> colName c) $ zip vals cols
    -- collect (constructor) constraints from individual relations
    predconstr = mkExpr $ conj 
                 $ map (\(ERelPred _ rname as, tname) -> 
                        let Relation{..} = getRelation r rname in
                        conj $ map (\(f,a) -> mkpconstr (eField (eVar tname) $ name f) (typ f) a) 
                             $ zip relArgs as) 
                       prednames
    mkpconstr :: Expr -> Type -> Expr -> Expr
    mkpconstr pref t (E EStruct{..}) = conj 
                                       $ (if' (length cs > 1) [eBinOp Eq pref (tagVal cs c)] []) ++
                                         (map (\(f,a) -> mkpconstr (eField pref $ name f) (typ f) a) $ zip fs exprFields)
        where TStruct _ cs = typ' r t
              Constructor _ c fs = getConstructor r exprConstructor
    mkpconstr _    _ _               = eBool True
    -- collect equality constraints
    eqconstr = andSep
               $ map (\(f, e:es) -> let ecols = e2cols r (typ f) e in
                                    andSep $ map (\e' -> let ecols' = e2cols r (typ f) e' in
                                                         andSep $ map (\(c1,c2) -> mkSqlFCol c1 <+> pp "=" <+> mkSqlFCol c2)
                                                                      $ zip ecols ecols') es) 
                     varcols
    -- collect non-predicate constraints (conds)
    arithconstr = mkExpr $ conj $ map subst conds
    -- substitute variable names with matching column names in expression
    subst e = exprFold subst' e
    subst' (EVar _ v) = head $ snd $ fromJust $ find ((== v) . name . fst) varcols
    subst' e          = E e

-- Only works for expressions whose variables are known to be non-NULL
-- (i.e., don't need to be coalesced)
mkExpr :: Expr -> Doc
mkExpr = mkExpr' . enode

mkExpr' :: ENode -> Doc
mkExpr' e@(EVar _ _)        = fcolName $ E e
mkExpr' e@(EField _ _ _)    = fcolName $ E e
mkExpr' e@(EBool _ _)       = mkVal $ E e
mkExpr' e@(EString _ _)     = mkVal $ E e
mkExpr' e@(EBit _ _ _)      = mkVal $ E e
mkExpr'   (EUnOp _ Not e)   = parens $ pp "not" <+> mkExpr e
mkExpr'   (EBinOp _ op l r) = parens $ 
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
         _      -> error $ "SQL.mkExpr EBinOp " ++ show op
    where l' = mkExpr l
          r' = mkExpr r 
mkExpr'   (ETyped _  e _)   = mkExpr e
mkExpr'   e                 = error $ "SQL.mkExpr" ++ show e


mkColumn :: Refine -> Field -> Doc
mkColumn r f = mkColumn' r (fieldType f) $ eVar $ name f

mkColumn' :: Refine -> Type -> Expr -> Doc
mkColumn' r t e = vcat $ punctuate comma 
                  $ map (\(e', t', _) -> colName e' <+> mkScalarType r t')
                  $ e2cols r t e
    
colName :: Expr -> Doc
colName = pp . replace "." "$" . render . pp

fcolName :: Expr -> Doc
fcolName e = let (tname, rest) = span (/= '.') $ render $ pp e in
             pp $ tname ++ "." ++ (replace "." "$" $ tail rest)

field2cols :: Refine -> Relation -> Expr -> [Expr]
field2cols r rel e = map sel1 $ e2cols r (exprType r (CtxRelKey rel) e) e

e2cols :: Refine -> Type -> Expr -> [(Expr, Type, Bool)]
e2cols r t e = e2cols' r t $ Just e

e2cols' :: Refine -> Type -> Maybe Expr -> [(Expr, Type, Bool)]
e2cols' r t (Just (E (ETyped _ e _))) = e2cols' r t $ Just e
e2cols' r t me = 
    case typ' r t of
         TStruct _ cs  -> let needtag = length cs > 1 in
                          case me of 
                               Nothing ->                   (if' needtag [(defVal $ tagType cs, tagType cs, False)] []) ++
                                                            (concatMap (\f -> e2cols' r (typ f) Nothing) $ structFields cs)
                               Just (E (EStruct _ c fs)) -> let Constructor _ _ as = getConstructor r c in
                                                                (if' needtag [(tagVal cs c, tagType cs, False)] []) ++ 
                                                                (concatMap (\f -> e2cols' r (typ f) $ fmap (fs !!) $ elemIndex f as) 
                                                                           $ structFields cs)
                               Just e                    -> (if' needtag [(e, tagType cs, False)] []) ++
                                                            ((if' needtag (map (\(e', t', _) -> (e', t', True))) id)
                                                             $ concatMap (\f -> e2cols' r (typ f) $ Just $ eField e $ name f)
                                                             $ structFields cs)
         _             -> maybe [(defVal t, t, False)] (\e -> [(e, t, False)]) me

mkScalarType :: Refine -> Type -> Doc
mkScalarType r t = mkScalarType' (typ' r t)

mkScalarType' :: Type -> Doc
mkScalarType' (TStruct _ cs)         = mkScalarType' $ tBit $ bitWidth $ length cs - 1
mkScalarType' (TBool _)              = pp "boolean"
mkScalarType' (TString _)            = pp "text"
mkScalarType' (TBit _ w) | w < 16    = pp "smallint"
                         | w < 32    = pp "int"
                         | w < 64    = pp "bigint"
                         | otherwise = pp "bit" <> (parens $ pp w)
mkScalarType' t                      = error $ "SQL.mkScalarType " ++ show t

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

mkVal :: Expr -> Doc
mkVal (E (EBool _ True))  = pp "true"
mkVal (E (EBool _ False)) = pp "false"
mkVal (E (EString _ str)) = pp $ show str
mkVal (E (EBit _ w v)) | w < 64    = pp v
                       | otherwise = pp $ "B'" ++ (map ((\b -> if' b '1' '0') . testBit v) [0..w-1]) ++ "'"
mkVal e                   = error $ "SQL.mkVal " ++ show e

mkConstraint :: Refine -> Relation -> Constraint -> (Doc, Doc)
mkConstraint r rel (PrimaryKey _ fs)           = 
    (pp "primary key" <+> (parens $ commaSep $ concatMap (map colName . field2cols r rel) fs), empty)
mkConstraint r rel (ForeignKey _ fs rname fs') = 
    ( let rel' = getRelation r rname in
      pp "foreign key" <+> 
      (parens $ commaSep $ concatMap (map colName . field2cols r rel) fs) <+>
      pp "references" <+> 
      (pp rname <+> (parens $ commaSep $ concatMap (map colName . field2cols r rel') fs'))
    , empty)
mkConstraint r rel (Unique _ fs) = 
    ( empty,
      pp "create unique index on" <+> (pp $ name rel) <+>
      (parens $ commaSep
       $ map mkSqlCol
       $ concatMap (\f -> e2cols r (exprType r (CtxRelKey rel) f) f) fs) <> semi)
mkConstraint _ _   (Check _ _)                 = (empty, empty)
--error "mkConstraint check is undefined"


mkSqlCol :: (Expr, Type, Bool) -> Doc
mkSqlCol (e, _, False) = colName e
mkSqlCol (e, t, True)  = pp "coalesce" <> (parens $ colName e <> comma <+> (mkVal $ defVal t))

mkSqlFCol :: (Expr, Type, Bool) -> Doc
mkSqlFCol (e, _, False) = fcolName e
mkSqlFCol (e, t, True)  = pp "coalesce" <> (parens $ fcolName e <> comma <+> (mkVal $ defVal t))
