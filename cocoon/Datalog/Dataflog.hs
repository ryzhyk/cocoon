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

-- Datalog implementation on top of the differential Dataflow library:

{-# LANGUAGE RecordWildCards, ImplicitParams, LambdaCase, OverloadedStrings #-}

module Datalog.Dataflog (mkRust, mkRule) where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import Data.Bits
import Data.Tuple.Select
import qualified Data.Graph.Inductive as G 

import Util
import Name
import PP
import Ops
import SMT.SMTSolver
import Datalog.Datalog

data DFSession = DFSession { dfQ     :: SMTQuery
                           , dfRels  :: [Relation]}

hname :: Relation -> String
hname rel = "_" ++ name rel

ruleHeadRel :: Rule -> String
ruleHeadRel rl = n
    where ERelPred n _ = ruleHead rl

ruleBodyRels :: Rule -> [String]
ruleBodyRels rl = nub $ ruleBodyRels' $ ruleBody rl

ruleBodyRels' :: Expr -> [String]
ruleBodyRels' (ERelPred n _)             = [n]
ruleBodyRels' (EUnOp Not (ERelPred n _)) = [n]
ruleBodyRels' (EBinOp And l r)           = ruleBodyRels' l ++ ruleBodyRels' r
ruleBodyRels' _                          = []

mkRust :: [Struct] -> [Function] -> [Relation] -> [Rule] -> Doc
mkRust structs funs rels rules = 
        ("let" <+> (tuple retvars) <+> "= worker.dataflow::<u64,_,_>(move |outer| {") $$
        (nest' $ vcat $ map mkSCC sccs) $$
        (tuple retvals <> semi) $$
        "}"
    where
    retvars = concatMap (\rl -> ["mut" <+> (pp $ hname rl), pp $ name rl]) rels
    retvals = concatMap (\rl -> [(pp $ hname rl), pp $ name rl]) rels
    q = SMTQuery structs [] funs []
    df = DFSession q rels
    relidx rel = fromJust $ findIndex ((== rel) . name) rels
    -- graph with relations as nodes and edges labeled with rules (labels are not unique)
    relgraph = G.insEdges (concatMap (\rule -> let r1 = relidx (ruleHeadRel rule) in
                                               map (\n2 -> let r2 = relidx n2
                                                           in (r2, r1, rule)) $ ruleBodyRels rule) 
                                     rules)
               $ G.insNodes (zip [0..] rels) (G.empty :: G.Gr Relation Rule)
    -- build a graph of scc's (edges = rules connecting relations in different scc's)
    sccgraph = grGroup relgraph $ G.scc relgraph
    -- topologically sort the scc graph
    sccs = G.topsort sccgraph
    
    -- For each scc:
    --  apply non-recursive rules for relations in the scc
    --  generate nested scope
    mkSCC :: G.Node -> Doc
    mkSCC sc = 
        let ?s = df in
        let screls = fromJust $ G.lab sccgraph sc
            collects = map (mkRelDecl . (rels !!)) screls
            rs = map (\r -> "let" <+> (pp $ ruleHeadRel r) <+> "=" <+> (pp $ ruleHeadRel r) <> ".concat(&" <> mkRule r <> ");") 
                 $ filter (all (\rel -> notElem (relidx rel) screls) . ruleBodyRels) -- non-recursive rules only
                 $ nub $ map sel3 $ G.inn sccgraph sc
            child = mkChildScope screls
        in vcat $ collects ++ rs ++ [child]

    mkChildScope :: [G.Node] -> Doc
    mkChildScope screls =
        let ?s = df in
        let header = "let" <+> (tuple $ map (pp . name . (rels !!)) screls) <+> "= outer.scoped::<u64,_,_>(|inner| {"
            -- rules in this scope
            scrules = nub $ map sel3 $ G.labEdges $ G.delNodes (G.nodes relgraph \\ screls) relgraph 
            -- relations imported into the scope
            imprels = nub $ concatMap ruleBodyRels scrules
            -- relations enter the scope
            imports = map (\rel -> "let mut" <+> pp rel <+> "= Variable::from(&" <> pp rel <> ".enter(inner));") imprels
            -- rules
            rs = map (\r -> ("let _ir =" <+> mkRule r <> semi) $$
                            ((pp $ ruleHeadRel r) <> ".add(&_ir);")) scrules
            -- exported relations leave the scope
            exports = tuple $ map ((\rel -> (pp $ name rel) <> ".leave()") . (rels !!)) screls
        in if' (null scrules) empty $ header $$ (nest' $ vcat $ imports ++ rs ++ [exports]) $$ "});"

mkRelDecl :: Relation -> Doc 
mkRelDecl rel = "let (mut" <+> n' <> comma <+> n <> ") = outer.new_collection::<" <> tuple args <> ",isize>();"
    where n  = pp $ name rel
          n' = pp $ hname rel
          args = map (mkType . varType) $ relArgs rel

commaSep = hsep . punctuate comma
commaCat = hcat . punctuate comma

tuple xs = tuple_ $ filter (/= empty) xs
tuple_ []  = empty
tuple_ [x] = x
tuple_ xs  = parens $ commaCat xs

tuple' xs = tuple_' $ filter (/= empty) xs
tuple_' []  = parens empty
tuple_' [x] = x
tuple_' xs  = parens $ commaCat xs

lambda :: Doc -> Doc -> Doc
lambda as e = "|" <> as <> "|" <+> e

mkType :: Type -> Doc
mkType TBool                = "bool"
mkType TInt                 = "BigUint"
mkType TString              = "String"
mkType (TBit w) | w <= 8    = "u8"
                | w <= 16   = "u16"
                | w <= 32   = "u32"
                | w <= 64   = "u64"
                | otherwise = "BigUint"
mkType (TStruct s)          = pp s
mkType TArray{}             = error "not implemented: Dataflog.mkType TArray"

mkStruct :: Struct -> Doc
mkStruct (Struct n cs) = "#[derive(Eq, PartialOrd, PartialEq, Ord, Debug, Clone, Hash)]" $$
                         enum $$
                         def $$    
                         pp ("unsafe_abomonate!(" ++ n ++ ");")
    where 
    enum = ("enum" <+> pp n <+> "{") $$
           (nest' $ vcat $ punctuate comma cs') $$
           "}"
    cs' = map (\case
                Constructor c [] -> pp c
                Constructor c fs -> pp c <+> "{" <> (commaSep $ map (\(Var v t) -> pp v <> ":" <+> mkType t) fs) <> "}") cs
    Constructor cn cas : _= cs
    defas = case cas of
                 [] -> empty
                 _  -> "{" <> (commaSep $ map (\a -> pp (name a) <> ": Default::default()") cas) <> "}"
    def = ("impl Default for" <+> pp n <+> "{") $$
          (nest' $ "fn default() -> " <+> pp n <+> "{" $$ (nest' $ pp n <> "::" <> pp cn <> defas <> "}")) $$
          "}"
    
mkRule :: (?s::DFSession) => Rule -> Doc
mkRule rule@Rule{..} = mkRuleP rule [] [] empty (order [] preds npreds) conds
    where 
    -- decompose the rule into a list of relatinal predicates and arithmetic constraints
    (preds, npreds, conds) = decompose ruleBody
    decompose (EBinOp And x xs)        = let (ps1, nps1, cs1) = decompose x 
                                             (ps2, nps2, cs2) = decompose xs 
                                         in (ps1 ++ ps2, nps1 ++ nps2, cs1 ++ cs2)
    decompose p@ERelPred{}             = ([p], [],  [])
    decompose p@(EUnOp Not ERelPred{}) = ([],  [p], [])
    decompose c                        = ([],  [],  [c])
    
    -- sort so that negated predicates appear immediately after all their variables have been introduced
    order _ [] nps = nps
    order vs (p:ps) nps = p : nps' ++ order vs' ps nps''
        where vs' = nub $ vs  ++ exprVars p
              (nps', nps'') = partition (\np -> null $ exprVars np \\ vs') nps

{- Recursive step of rule translation: map_join
 jvars - variables that will be used in the next join.  The prefix of
         the rule computed so far has been pivoted to return a
         relation of the form ((jvars), vars)
 vars  - other variables that occur in the prefix and have not been
         discarded yet (because they are used either in subsequent
         joins or in the head of the rule)
 pref  - prefix of the rule computed so far
 preds - remaining predicates in the body of the rule
 conds - remaining arithmetic constraints in the body of the rule
 -}
mkRuleP :: (?s::DFSession) => Rule -> [String] -> [String] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleP Rule{..} [] vars pref [] [] = 
    -- pref.map(|<vars>|(<args>))
    pref <> "." <> "map" <> (parens $ "|" <> _vars <> "|" <+> _args)
    where ERelPred _ args = ruleHead
          _vars = tuple $ map pp vars
          _args = tuple $ map mkExpr args
mkRuleP rule [] vars pref [] conds = 
    mkRuleC rule [] vars pref [] conds
mkRuleP rule@Rule{..} jvars vars pref preds conds = 
    mkRuleC rule jvars' vars' pref' preds' conds
    where 
    p:preds' = preds
    -- variables in p
    pvars = exprVars p
    -- care set - variables we want to keep around for future joins
    care = sort $
           (nub $ concatMap exprVars preds' ++ concatMap exprVars conds ++ exprVars ruleHead)
           `intersect` 
           (nub $ jvars ++ vars ++ pvars)
    -- care variables in p, except join variables 
    care' = sort $ (pvars \\ jvars) `intersect` care
    -- join vars for the next join
    jvars' = case preds' of
                  []      -> []
                  p':_ -> care `intersect` exprVars p'
    vars' = care \\ jvars'
    (sign, rname, args) = case p of
                               EUnOp Not (ERelPred rn as) -> (False, rn, as)
                               ERelPred rn as             -> (True,  rn, as)
                               _                          -> error $ "Dataflog.mkRuleP: invalid predicate " ++ show p
    Relation{..} = fromJust $ find ((== rname) . name) $ dfRels ?s
    _args = tuple $ map mkExpr args
    _vars = tuple $ map pp vars
    _jvars = tuple' $ map pp jvars
    _jvars' = tuple' $ map pp jvars'
    _care' = map pp care'
    _vars' = map pp vars'
    filters = filter (/= empty) $ map (\(ra, a) -> mkFilter (EVar $ name ra) a) $ zip relArgs args
    _filters = case filters of
                    [] -> empty
                    _  -> "." <> "filter" <> (parens $ lambda _args (hsep $ intersperse ("&&") filters))
    pref' = if' (pref == empty)
                -- <rname>.filter(<filters>).map(|<args>|(<jvars'>, <vars'>))
                (pp rname <> _filters <>
                             "." <> "map" <> (parens $ lambda _args (tuple $ _jvars':_vars') )) 
                (if' sign
                     -- <pref>.join_map(<rname>.filter(<filters>).map(|<args>|(<jvars>, <care'>)), |(<jvars>, <vars>, <care'>)|(<jvars'>, <vars'>))
                     (pref <> "." <> "join_map" <> (parens 
                              (pp rname <> _filters <> "." <> "map" <> (parens $ lambda _args (tuple $ _jvars:_care'))) <> comma <+>
                              ("|" <> tuple [_jvars, _vars, tuple _care'] <> "|" <+> (tuple $ _jvars':_vars'))))
                     -- <pref>.antijoin(<rname>.filter(<filters>).map(|<args>|<jvars>)).map(|(<jvars>, <vars>)|(<jvars'>, <vars'>))
                     (pref <> "." <> "antijoin" <> 
                              (parens $ pp rname <> _filters <> "." <> "map" <> (parens $ lambda _args _jvars)) <>
                              "." <> "map" <> 
                              (parens $ lambda (tuple [_jvars, _vars]) (tuple $ _jvars': _vars'))))

mkFilter :: (?s::DFSession) => Expr -> Expr -> Doc
mkFilter e pat | pat' == "_" = empty
               | otherwise = "match" <+> mkExpr e <+> 
                             "{" <> pat' <+> "=>" <+> "true" <> comma <+> "_" <+> "=>" <+> "false" <> "}"
    where pat' = mkFilter' pat

mkFilter' :: (?s::DFSession) => Expr -> Doc
mkFilter' (EVar _) = "_"
mkFilter' (EStruct c as) | length structCons == 1 && (all (== "_") afs) = "_"
                         | otherwise = pp structName <> "::" <> pp c <> as'
    where Struct{..} = getStruct (dfQ ?s) c 
          args = consArgs $ getConstructor (dfQ ?s) c
          afs = map mkFilter' as
          as' = case as of
                     [] -> empty
                     _  -> "{" <> (commaSep $ map (\(arg, a) -> pp (name arg) <> ":" <+> a) 
                                               $ zip args afs) <> "}"
mkFilter' e = error $ "Dataflog.mkFilter' " ++ show e

mkExpr :: (?s::DFSession) => Expr -> Doc
mkExpr (EVar v)             = pp v
mkExpr (EApply f as)        = pp f <> (parens $ commaSep $ map mkExpr as)
mkExpr (EField _ s f)       = mkExpr s <> "." <> pp f
mkExpr (EBool True)         = "true"
mkExpr (EBool False)        = "false"
mkExpr (EBit w i) | w<=64   = pp i
                  | otherwise = mkExpr $ EInt i
mkExpr (EInt i)             = "BigUint::parse_bytes" <> 
                              (parens $ "b\"" <> pp i <> "\"" <> comma <+> "10") <> ".unwrap()"
mkExpr (EString s)          = pp $ "\"" ++ s ++ "\""
mkExpr (EStruct c as)       = (pp $ name s) <> "::" <> pp c <> "{"  <> 
                              (commaSep $ map (\(arg, a) -> (pp $ name arg) <> ":" <+> mkExpr a) $ zip args as) <> "}"
    where s = getStruct (dfQ ?s) c
          args = consArgs $ getConstructor (dfQ ?s) c
mkExpr EIsInstance{}        = error "not implemented: Dataflog.mkExpr EIsInstance"
mkExpr (EBinOp op e1 e2)    = 
    case op of
         Eq     -> f "=="
         Neq    -> f "!="
         Lt     -> f "<"
         Gt     -> f ">"
         Lte    -> f "<="
         Gte    -> f ">="
         And    -> f "&&"
         Or     -> f "||"
         Plus   -> f "+"
         Minus  -> f "-"
         Mod    -> f "%"
         ShiftR -> f ">>"
         ShiftL -> f "<<"
         Impl   -> mkExpr $ EBinOp Or (EUnOp Not e1) e2
         Concat -> error "not implemented: Dataflog.mkExpr Concat"
    where f o = parens $ mkExpr e1 <+> o <+> mkExpr e2

mkExpr (EUnOp Not e)        = parens $ "!" <> mkExpr e
mkExpr (ESlice e h l)       = let e' = mkExpr e
                                  e1 = if' (l == 0) e' (parens $ e' <+> ">>" <+> pp l)
                                  mask = foldl' setBit 0 [0..(h-l)]
                                  mask' = mkExpr $ EBit (h-l+1) mask
                              in parens $ e1 <+> "&" <+> mask'
mkExpr (ECond [] d)         = mkExpr d
mkExpr (ECond ((c,e):cs) d) = "if" <+> mkExpr c <+> "{" <> mkExpr e <> "}" <+> 
                              "else" <+> (mkExpr $ ECond cs d)
mkExpr ERelPred{}           = error "not implemented: Dataflog.mkExpr ERelPred"

{- Recursive step of rule translation: filter based on arith constraints 
   whose variables have been introduced by now
 -}
mkRuleC :: (?s::DFSession) => Rule -> [String] -> [String] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleC rule@Rule{..} jvars vars pref preds conds =
    if' (null conds')
        (mkRuleP rule jvars vars pref preds conds)
        (mkRuleP rule jvars vars pref' preds conds'')
    where 
    _jvars = tuple' $ map pp jvars
    _vars = map pp vars
    (conds', conds'') = partition (\e -> null $ exprVars e \\ (jvars ++ vars)) conds
    _conds = mkExpr $ conj conds'
    f = "." <> "filter" <> (parens $ "|" <> (tuple $ _jvars:_vars) <> "|" <+> _conds)
    pref' = pref <> f
