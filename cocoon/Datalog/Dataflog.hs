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

-- Datalog implementation on top of the differential Dataflow library:

{-# LANGUAGE RecordWildCards, ImplicitParams, LambdaCase, OverloadedStrings #-}

module Datalog.Dataflog (mkRust) where

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
import Datalog.DataflogTemplate

hname :: Relation -> String
hname rel = "_" ++ name rel

commaSep = hsep . punctuate comma
commaCat = hcat . punctuate comma

tuple xs = tuple_ $ filter (/= empty) xs
tuple_ []  = parens empty
tuple_ [x] = x
tuple_ xs  = parens $ commaCat xs

reftuple xs = reftuple_ $ map (filter (/= empty)) xs
reftuple_ [[x]]  = x
reftuple_ xss    = "&" <> reftuple__ xss

reftuple__ [xs] = reftuple___ xs
reftuple__ xss  = parens $ commaSep $ map reftuple___ xss

reftuple___ []  = parens empty
reftuple___ [x] = "ref" <+> x
reftuple___ xs  = parens $ commaCat $ map ("ref" <+>) xs

lambda :: Doc -> Doc -> Doc
lambda as e = "|" <> as <> "|" <+> e

lambdam :: Doc -> Doc -> Doc
lambdam as e = "|_x_| match _x_ {" <> as <+> "=>" <+> e <> ", _ => unreachable!()}"

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

mkRust ::  [Struct] -> [Function] -> [Relation] -> [Rule] -> Doc
mkRust structs funs rels rules = 
    let ?q = SMTQuery structs [] funs [] in
    let ?rels = rels in
    let decls = vcat $ map mkStruct structs
        logic = mkRules rules
        facts = mkFacts rels
        relations = mkRels rels
        sets  = mkSets rels
        handlers = mkHandlers rels
        advance = mkAdvance rels
        cleanup = mkCleanup rels
        undo = mkUndo rels
    in dataflogTemplate decls facts relations sets logic advance cleanup undo handlers

mkCleanup :: [Relation] -> Doc
mkCleanup rels =
    "macro_rules! delta_cleanup {" $$
    "    () => {{" $$
    (nest' $ nest' $ vcat $ map (\rel -> "__rDelta" <> (pp $ name rel) <> ".borrow_mut().clear();") $ filter (not . relIsView) rels) $$
    "    }}" $$
    "}"

mkUndo :: [Relation] -> Doc
mkUndo rels = 
    "macro_rules! delta_undo {" $$
    "    () => {{" $$
    (nest' $ nest' $ vcat $ map (\rel -> 
            let n = pp $ name rel in
            "let mut d = __rDelta" <> n <> ".borrow().clone();" $$
            "for (k,v) in d.drain() {" $$
            "    if v == 1 {" $$
            "        remove!(_" <> n <> ", _r" <> n <> ", k);" $$
            "    } else if v == -1 {" $$
            "        insert!(_" <> n <> ", _r" <> n <> ", k);" $$
            "    };" $$
            "};") $ filter (not . relIsView) rels) $$
    "   }}" $$
    "}"

mkAdvance :: [Relation] -> Doc
mkAdvance rels = 
    "macro_rules! advance {" $$
    "    () => {{" $$
    (nest' $ nest' $ vcat $ map (\rel -> "_" <> pp (name rel) <> ".advance_to(epoch);") rels) $$
    (nest' $ nest' $ vcat $ map (\rel -> "_" <> pp (name rel) <> ".flush();") rels) $$
    "    }}"$$
    "}"

mkFacts :: [Relation] -> Doc
mkFacts rels = 
    "#[derive(Serialize, Deserialize, Debug)]" $$
    "enum Fact {" $$
    (nest' $ vcat $ punctuate comma $ map (\rel -> pp (name rel) <> (parens $ commaSep $ map (mkType . varType) $ relArgs rel)) rels)
    $$ "}"

mkRels :: [Relation] -> Doc
mkRels rels = 
    "#[derive(Serialize, Deserialize, Debug)]" $$
    "enum Relation {" $$
    (nest' $ vcat $ punctuate comma $ map (pp . name) rels)
    $$ "}"

mkSets :: [Relation] -> Doc
mkSets rels = 
    (vcat
     $ map (\rel -> let n = pp $ name rel
                        args = commaSep $ map (mkType . varType) $ relArgs rel in
                    ("let mut _r" <> n <> ": Rc<RefCell<HashSet<(" <> args <> ")>>> = Rc::new(RefCell::new(HashSet::new()));") $$
                    ("let mut _w" <> n <> ": Rc<RefCell<HashSet<(" <> args <> ")>>> = _r" <> n <> ".clone();")) rels)
    $$
    (vcat
     $ map (\rel -> let n = pp $ name rel
                        args = commaSep $ map (mkType . varType) $ relArgs rel in
                    ("let mut __rDelta" <> n <> ": Rc<RefCell<HashMap<(" <> args <> "), i8>>> = Rc::new(RefCell::new(HashMap::new()));") $$
                    ("let mut __wDelta" <> n <> ": Rc<RefCell<HashMap<(" <> args <> "), i8>>> = __rDelta" <> n <> ".clone();")) 
     $ filter (not . relIsView) rels)

mkHandlers :: [Relation] -> Doc
mkHandlers = vcat .
    map (\rel -> let n = pp $ name rel 
                     as = commaCat $ mapIdx (\_ i -> "a" <> pp i) $ relArgs rel in
                 ("Request::add(Fact::" <> n <> "(" <> as <> ")) => insert_resp!(_" <> n <> ", _r" <> n <> ", (" <> as <> ")),") $$
                 ("Request::del(Fact::" <> n <> "(" <> as <> ")) => remove_resp!(_" <> n <> ", _r" <> n <> ", (" <> as <> ")),") $$
                 ("Request::chk(Relation::" <> n <> ") => check!(_r" <> n <> "),") $$
                 ("Request::enm(Relation::" <> n <> ") => enm!(_r" <> n <> "),"))

mkRules :: (?q::SMTQuery, ?rels::[Relation]) => [Rule] -> Doc
mkRules rules = 
        ("let" <+> tuple retvars <+> "= worker.dataflow::<u64,_,_>(move |outer| {") $$
        (nest' $ vcat $ map mkSCC sccs) $$
        (nest' $ vcat distinct) $$
        (nest' $ vcat probes) $$
        (nest' $ tuple retvals) $$
        "});"
    where
    rels = ?rels
    retvars = map (\rl -> "mut" <+> (pp $ hname rl)) rels
    distinct = map (\rl -> "let " <> pp (name rl) <> " = " <> pp (name rl) <> ".distinct();") rels
    probes = map (\rl -> let n = pp $ name rl in
                         if relIsView rl 
                            then n <> ".inspect(move |x| upd(&_w" <> n <> ", &(x.0), x.2)).probe_with(&mut probe1)" <> semi
                            else n <> ".inspect(move |x| xupd(&_w" <> n <> ", &__wDelta" <> n <> ", &(x.0), x.2)).probe_with(&mut probe1)" <> semi) 
                 rels

    retvals = map (\rl -> (pp $ hname rl)) rels
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
        let screls = fromJust $ G.lab sccgraph sc
            collects = map (mkRelDecl . (rels !!)) screls
            rs = map (\r -> "let" <+> (pp $ ruleHeadRel r) <+> "=" <+> (pp $ ruleHeadRel r) <> ".concat(&(" <> mkRule r <> "));") 
                 $ filter (all (\rel -> notElem (relidx rel) screls) . ruleBodyRels) -- non-recursive rules only
                 $ nub $ map sel3 $ G.inn sccgraph sc
            child = mkChildScope screls
        in vcat $ collects ++ rs ++ [child]

    mkChildScope :: [G.Node] -> Doc
    mkChildScope screls =
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


mkType :: Type -> Doc
mkType TBool                = "bool"
mkType TInt                 = "uint"
mkType TString              = "String"
mkType (TBit w) | w <= 8    = "u8"
                | w <= 16   = "u16"
                | w <= 32   = "u32"
                | w <= 64   = "u64"
                | otherwise = "uint"
mkType (TStruct s)          = pp s
mkType TArray{}             = error "not implemented: Dataflog.mkType TArray"

mkStruct :: Struct -> Doc
mkStruct (Struct n cs) = "#[derive(Eq, PartialOrd, PartialEq, Ord, Debug, Clone, Hash, Serialize, Deserialize)]" $$
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
    
mkRule :: (?q::SMTQuery, ?rels::[Relation]) => Rule -> Doc
mkRule rule = mkRuleP rule' [] [] empty (order [] preds npreds) conds
    where 
    rule'@Rule{..} = removeFields rule
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

-- Get rid of subexpressions of the form var.field. 
removeFields :: (?q::SMTQuery) => Rule -> Rule
removeFields rule@Rule{..} = 
    case vcons of
         [] -> rule
         _  -> let subst1 e@(EField _ (EVar v) f) = case lookup v vcons of
                                                         Nothing  -> e
                                                         _        -> EVar $ fvar v f
                   subst1 e                       = e
                   subst2 e@(EVar v) = case lookup v vcons of
                                            Nothing -> e
                                            Just c  -> EStruct (name c) $ map (\f -> EVar $ fvar v (name f)) $ consArgs c
                   subst2 e          = e
                   -- substiture: v -> C{v_f1, v_f1, ...}
                   --             v.f -> v_f
                   h = exprMap subst2 $ exprMap subst1 ruleHead
                   b = exprMap subst2 $ exprMap subst1 ruleBody
                   vs = concatMap (\v -> case lookup (name v) vcons of
                                              Just c -> map (\(Var f t) -> Var (fvar (name v) f) t) $ consArgs c
                                              _      -> [v]) ruleVars
                   -- update rule's variable list
                   rule' = Rule vs h b ruleId
               in removeFields rule'
    where
    -- collect all v.f subexpressions.
    vcons :: [(String, Constructor)]
    vcons = nub $ exprCollect f ruleHead ++ exprCollect f ruleBody
        where f (EField c (EVar v) _) = [(v, getConstructor ?q c)]
              f _                     = []
    fvar v f = "_" ++ v ++ "_" ++ f
    -- TODO: make sure constructors match
    -- vcons' = sortAndGroup fst vcons

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
mkRuleP :: (?q::SMTQuery, ?rels::[Relation]) => Rule -> [String] -> [String] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleP Rule{..} [] vars pref [] [] = 
    -- pref.map(|<vars>|(<args>))
    pref $$ ("." <> "map" <> (parens $ "|" <> _vars <> "|" <+> _args))
    where ERelPred _ args = ruleHead
          _vars = tuple $ map pp vars
          _args = tuple $ map (mkExpr False) args
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
    Relation{..} = fromJust $ find ((== rname) . name) ?rels
    _args = tuple $ map (mkExpr True) args
    _vars = tuple $ map pp vars
    _jvars = tuple $ map pp jvars
    _jvars' = case preds' of
                   [] -> []
                   _  -> [tuple $ map pp jvars']
    _jvars'' = case preds' of
                    [] -> []
                    _  -> [tuple $ map ((<> ".clone()") . pp) jvars']
    _care' = tuple $ map pp care'
    _vars' = tuple $ map pp vars'
    _vars'' = tuple $ map ((<> ".clone()") . pp) vars'
    _rargs = reftuple [map (pp . name) relArgs]
    filters = filter (/= empty) $ map (\(ra, a) -> mkFilter (EVar $ name ra) a) $ zip relArgs args
    _filters = case filters of
                    [] -> empty
                    _  -> "." <> "filter" <> (parens $ lambda _rargs (hsep $ intersperse ("&&") filters))
    pref' = if' (pref == empty)
                -- <rname>.filter(<filters>).map(|<args>|(<jvars'>, <vars'>))
                (pp rname <> (_filters
                              $$ ("." <> "map" <> (parens $ lambdam _args (tuple $ _jvars' ++ [_vars']) )))) 
                (if' sign
                     -- <pref>.join_map(<rname>.filter(<filters>).map(|<args>|(<jvars>, <care'>)), |(<jvars>, <vars>, <care'>)|(<jvars'>, <vars'>))
                     (pref $$ ("." <> "join_map" <> (parens $
                               "&" <> (parens $ (pp rname <> _filters <> "." <> "map" <> (parens $ lambdam _args (tuple [_jvars,_care'])))) <> comma <+>
                               ("|" <> commaSep [reftuple [map pp jvars], reftuple [map pp vars], reftuple [map pp care']] <> "|" <+> (tuple $ _jvars'' ++ [_vars''])))))
                     -- <pref>.antijoin(<rname>.filter(<filters>).map(|<args>|<jvars>)).map(|(<jvars>, <vars>)|(<jvars'>, <vars'>))
                     (pref $$ ("." <> "antijoin" <> 
                               (parens $ "&" <> (parens $ pp rname <> _filters <> "." <> "map" <> (parens $ lambdam _args _jvars))) $$
                               ("." <> "map" <> (parens $ lambda (tuple [_jvars, _vars]) (tuple $ _jvars' ++ [_vars']))))))

mkFilter :: (?q::SMTQuery) => Expr -> Expr -> Doc
mkFilter e pat | pat' == "_" = empty
               | otherwise = "match" <+> mkExpr False e <+> 
                             "{" <> pat' <+> "=>" <+> "true" <> comma <+> "_" <+> "=>" <+> "false" <> "}"
    where pat' = mkFilter' pat

mkFilter' :: (?q::SMTQuery) => Expr -> Doc
mkFilter' (EVar _) = "_"
mkFilter' (EStruct c as) | length structCons == 1 && (all (== "_") afs) = "_"
                         | otherwise = pp structName <> "::" <> pp c <> as'
    where Struct{..} = getConsStruct ?q c 
          args = consArgs $ getConstructor ?q c
          afs = map mkFilter' as
          as' = case as of
                     [] -> empty
                     _  -> "{" <> (commaSep $ map (\(arg, a) -> pp (name arg) <> ":" <+> a) 
                                               $ zip args afs) <> "}"
mkFilter' e = error $ "Dataflog.mkFilter' " ++ show e

mkExpr :: (?q::SMTQuery) => Bool ->  Expr -> Doc
mkExpr True  (EVar v)           = pp v
mkExpr False (EVar v)           = pp v <> ".clone()"
mkExpr p     (EApply f as)      = pp f <> (parens $ commaSep $ map (mkExpr p) as)
mkExpr p     (EField _ s f)     = mkExpr p s <> "." <> pp f
mkExpr _     (EBool True)         = "true"
mkExpr _     (EBool False)        = "false"
mkExpr p     (EBit w i) | w<=64   = pp i
                        | otherwise = mkExpr p $ EInt i
mkExpr _     (EInt i)             = "uint::parse_bytes" <> 
                                    (parens $ "b\"" <> pp i <> "\"" <> comma <+> "10") <> ".unwrap()"
mkExpr _     (EString s)          = pp $ "\"" ++ s ++ "\""
mkExpr p     (EStruct c as)       = (pp $ name s) <> "::" <> pp c <> "{"  <> 
                                    (commaSep $ map (\(arg, a) -> (pp $ name arg) <> ":" <+> mkExpr p a) $ zip args as) <> "}"
    where s = getConsStruct ?q c
          args = consArgs $ getConstructor ?q c
mkExpr _     EIsInstance{}        = error "not implemented: Dataflog.mkExpr EIsInstance"
mkExpr p     (EBinOp op e1 e2)    = 
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
         Impl   -> mkExpr p $ EBinOp Or (EUnOp Not e1) e2
         Concat -> error "not implemented: Dataflog.mkExpr Concat"
    where f o = parens $ mkExpr p e1 <+> o <+> mkExpr p e2
mkExpr p     (EUnOp Not e)        = parens $ "!" <> mkExpr p e
mkExpr p     (ESlice e h l)       = let e' = mkExpr p e
                                        e1 = if' (l == 0) e' (parens $ e' <+> ">>" <+> pp l)
                                        mask = foldl' setBit 0 [0..(h-l)]
                                        mask' = mkExpr p $ EBit (h-l+1) mask
                              in parens $ e1 <+> "&" <+> mask'
mkExpr p     (ECond [] d)         = mkExpr p d
mkExpr p     (ECond ((c,e):cs) d) = "if" <+> mkExpr p c <+> "{" <> mkExpr p e <> "}" <+> 
                                    "else" <+> (mkExpr p $ ECond cs d)
mkExpr _     ERelPred{}           = error "not implemented: Dataflog.mkExpr ERelPred"

{- Recursive step of rule translation: filter based on arith constraints 
   whose variables have been introduced by now
 -}
mkRuleC :: (?q::SMTQuery, ?rels::[Relation]) => Rule -> [String] -> [String] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleC rule@Rule{..} jvars vars pref preds conds =
    if' (null conds')
        (mkRuleP rule jvars vars pref preds conds)
        (mkRuleP rule jvars vars pref' preds conds'')
    where 
    _jvars = case preds of
                  [] -> []
                  _  -> [map pp jvars]
    _vars = map pp vars
    (conds', conds'') = partition (\e -> null $ exprVars e \\ (jvars ++ vars)) conds
    _conds = mkExpr False {-$ exprMap (\case
                                EVar v -> EVar $ "(*" ++ v ++ ")"
                                e      -> e)-} $ conj conds'
    f = "." <> "filter" <> (parens $ "|" <> (reftuple $ _jvars ++ [_vars]) <> "|" <+> _conds)
    pref' = pref $$ f
