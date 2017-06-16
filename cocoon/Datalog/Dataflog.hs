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


module Datalog.Dataflog (mkRule) where

data DFSession = DFSession { dfStructs   = [Struct]
                           , dfRelations = [Relation]}

-- structs

-- rule graph
-- DAG of connected components 

commaSep = hsep $ punctuate comma
commaCat = hcat $ punctuate comma

mkRule :: Rule -> Doc
mkRule rule@Rule{..} = mkRuleP rule [] [] empty preds conds
    where 
    -- decompose the rule into a list of relatinal predicates and arithmetic constraints
    (preds, conds) = decompose ruleRHS
    decompose (EBinOp And x xs)       = let (ps1, cs1) = decompose x 
                                            (ps2, cs2) = decompose xs 
                                        in (ps1 ++ ps2, cs1 ++ cs2)
    decompose p@ERelPred{}            = ([p], [])
    decompose p(EUnOp Not ERelPred{}) = ([p], [])
    decompose c                       = ([],  [c])

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
mkRuleP :: (?s::DFSession) => Rule -> [Var] -> [Var] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleP Rule{..} [] vars pref [] [] = 
    -- pref.map(|<vars>|(<args>))
    pref <> pp "." <> pp "map" <> (parens $ pp "|" <> _vars <> pp "|" <+> args)
    where ERelPred rname args = ruleHead
          _vars = tuple $ map (pp . name) vars
          _args = tuple $ map mkExpr args
mkRuleP rule [] vars pref [] conds = 
    mkRuleC rule [] vars pref [] conds
mkRuleP rule@Rule{..} jvars vars pref preds conds = 
    mkRuleC rule jvars' vars' pref' preds' conds
    where 
    pred:preds' = preds
    -- variables in pred
    pvars = exprVars pred
    -- care set - variables we want to keep around for future joins
    care = sort $
           (nub $ concatMap exprVars preds' ++ concatMap exprVars conds ++ exprVars ruleHead)
           `intersect` 
           (nub $ jvars ++ vars ++ pvars)
    -- care variables in pred, except join variables 
    care' = sort $ (pvars \\ jvars) `intersect` care
    -- join vars for the next join
    jvars' = case preds' of
                  []      -> []
                  pred':_ -> care `intersect` exprVars pred'
    vars' = care \\ jvars'
    (sign, rname, args) = case pred of
                               EUnOp Not (ERelPred rname args) -> (False, rname, args)
                               ERelPred rname args             -> (True,  rname, args)
    rel@Relation{..} = fromJust $ find ((== rname) . name) $ dfRelations ?s
    _args = tuple $ map mkExpr args
    _vars = tuple $ map (pp . name) vars
    _jvars = tuple' $ map (pp . name) jvars
    _jvars' = tuple' $ map (pp . name) jvars'
    _care' = map (pp . name) care'
    _vars' = map (pp . name) vars'
    filters = mapMaybe (\(ra, a) -> mkFilter (EVar $ name ra) a) $ zip relArgs args
    _filters = case filters of
                    [] -> empty
                    _  -> pp "." <> pp "filter" <> (parens $ pp "|" <> _args <> pp "|" <+> (hsep $ intercalate "&&" filters))
    pref' = if' pref == empty
                -- <rname>.filter(<filters>).map(|<args>|(<jvars'>, <vars'>))
                (pp rname <> _filters <>
                             pp "." <> pp "map" <> (parens $ pp "|" <> _args <> pp "|" <+> (tuple $ _jvars':_vars') ))
                -- <pref>.join_map(<rname>.filter(<filters>).map(|<args>|(<jvars>, <care'>)), |(<jvars>, <vars>, <care'>)|(<jvars'>, <vars'>))
                (pref <> pp "." <> pp "join_map" <> (parens 
                         (pp rname <> _filters <> pp "." <> pp "map" <> (parens $ pp "|" <> _args <> pp "|" <+> (tuple $ _jvars:_care') )) <> comma <+>
                         (pp "|" <> (tuple $ [_jvars, _vars, tuple _care']) <> pp "|" <+> (tuple $ _jvars':_vars')))

    tuple xs = tuple_ $ filter (/= empty) xs'
    tuple_ []  = empty
    tuple_ [x] = x
    tuple_ xs  = parens $ commaCat xs

    tuple' xs = tuple_' $ filter (/= empty) xs'
    tuple_' []  = parens empty
    tuple_' [x] = x
    tuple_' xs  = parens $ commaCat xs


mkFilter :: (?s::DFSession) => Expr -> Expr -> Doc
mkFilter e pat = pp "match" <+> mkExpr e <+> 
                 pp "{" <> pat' <+> pp "=>" <+> pp "true" <> comma <+> pp "_" <+> pp "=>" <+> pp "false" <> pp "}"
    where pat' = mkFilter' pat

mkFilter' :: (?s::DFSession) => Expr -> Doc
mkFilter' (EVar _)       = pp "_"
mkFilter' (EStruct c as) = pp structName <> pp "::" <> pp c <> as'
    where Struct{..} = getStruct ?s c 
          (_, args)= getConstructor ?s c
          as' = case as of
                     [] -> empty
                     _  -> pp "{" <> (commaSep $ map (\(arg, a) -> pp (name arg) <> pp ":" <+> mkFilter' a) 
                                               $ zip args as) <> pp "}"

mkExpr :: (?s::DFSession) => Expr -> Doc
mkExpr (EVar v)             = pp v
mkExpr (EApply f as)        = pp f <> (parens $ commaSep $ map mkExpr as)
mkExpr (EField s f)         = mkExpr s <> pp "." <> pp f
mkExpr (EBool True)         = pp "true"
mkExpr (EBool False)        = pp "false"
mkExpr (EBit w i) | w<=64   = pp i
                  | otherwise = mkExpr $ EInt i
mkExpr (EInt i)             = pp "BigUint::parse_bytes" <> 
                              (parens $ pp "b\"" <> pp i <> "\"" <> comma <+> pp "10") <> pp ".unwrap()"
mkExpr (EString s)          = pp $ "\"" ++ s ++ "\""
mkExpr (EStruct c as)       = (pp $ name s) <> pp "::" <> pp c <> pp "{"  <> 
                              (commaSep $ map (\(arg, a) -> (pp $ name args) <> pp ":" <+> mkExpr a) $ zip args as) <> pp "}"
    where s = getStruct ?s c
          (_, args) = getConstructor ?s c
mkExpr EIsInstance{}        = error "not implemented: Dataflog.mkExpr EIsInstance"
mkExpr (EBinOp Impl e1 e2)  = mkExpr $ EBinOp Or (EUnOp Not e1) e2
mkExpr (EBinOp op e1 e2)    = parens $
    case op of
         Eq     -> e1' <+> pp "==" <+> e2'
         Neq    -> e1' <+> pp "!=" <+> e2'
         Lt     -> e1' <+> pp "<" <+> e2'
         Gt     -> e1' <+> pp ">" <+> e2'
         Lte    -> e1' <+> pp "<=" <+> e2'
         Gte    -> e1' <+> pp ">=" <+> e2'
         And    -> e1' <+> pp "&&" <+> e2'
         Or     -> e1' <+> pp "||" <+> e2'
         Plus   -> e1' <+> pp "+" <+> e2'
         Minus  -> e1' <+> pp "-" <+> e2'
         Mod    -> e1' <+> pp "%" <+> e2'
         ShiftR -> e1' <+> pp ">>" <+> e2'
         ShiftL -> e1' <+> pp "<<" <+> e2'
         Concat -> error "not implemented: Dataflog.mkExpr Concat"
    where e1' = mkExpr e1
          e2' = mkExpr e2
mkExpr (EUnOp Not e)        = parens $ pp "!" <> mkExpr e
mkExpr (ESlice e h l)       = let e' = mkExpr e
                                  e1 = if' (l == 0) e' (parens $ e' <+> pp ">>" <+> pp l)
                                  mask = foldl' setBit 0 [0..(h-l)]
                                  mask' = mkExpr $ EBit (h-l+1) mask
                                  e2 = parens $ e1 <+> pp "&" <+> mask'
mkExpr (ECond [] d)         = mkExpr d
mkExpr (ECond ((c,e):cs) d) = pp "if" <+> mkExpr c <+> pp "{" <> mkExpr e <> pp "}" <+> 
                              pp "else" <+> (mkExpr $ ECond cs d)
mkExpr ERelPred{}           = error "not implemented: Dataflog.mkExpr ERelPred"

{- Recursive step of rule translation: filter based on arith constraints 
   whose variables have been introduced by now
 -}
mkRuleC :: (?s::[DFSession]) => Rule -> [Var] -> [Var] -> Doc -> [Expr] -> [Expr] -> Doc
mkRuleC rule@Rule{..} jvars vars pref preds conds =
    if' null conds'
        (mkRuleP rule jvars vars pref preds conds)
        (mkRuleP rule jvars vars pref' preds conds'')
    where 
    _jvars = tuple' $ map (pp . name) jvars
    _vars = map (pp . name) jvars
    (conds', conds'') = partition (\e -> null $ exprVars e \\ (jvars ++ vars)) conds
    _conds = mkExpr $ conj conds'
    f = pp "." <> pp "filter" <> (parens $ pp "|" <> (tuple $ _jvars:_vars) <> pp "|" <+> _conds)
    pref' = pref <> f
