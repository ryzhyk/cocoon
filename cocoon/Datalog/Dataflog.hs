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

{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module Datalog.Dataflog (mkRust, mkRule) where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import Data.Bits

import Util
import Name
import PP
import Ops
import SMT.SMTSolver
import Datalog.Datalog

data DFSession = DFSession { dfQ     :: SMTQuery
                           , dfRels  :: [Relation]}

mkRust :: [Struct] -> [Function] -> [Relation] -> Doc
mkRust = undefined

-- structs

-- rule graph
-- DAG of connected components 

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
    pref <> pp "." <> pp "map" <> (parens $ pp "|" <> _vars <> pp "|" <+> _args)
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
                    _  -> pp "." <> pp "filter" <> (parens $ lambda _args (hsep $ intersperse (pp "&&") filters))
    pref' = if' (pref == empty)
                -- <rname>.filter(<filters>).map(|<args>|(<jvars'>, <vars'>))
                (pp rname <> _filters <>
                             pp "." <> pp "map" <> (parens $ lambda _args (tuple $ _jvars':_vars') )) 
                (if' sign
                     -- <pref>.join_map(<rname>.filter(<filters>).map(|<args>|(<jvars>, <care'>)), |(<jvars>, <vars>, <care'>)|(<jvars'>, <vars'>))
                     (pref <> pp "." <> pp "join_map" <> (parens 
                              (pp rname <> _filters <> pp "." <> pp "map" <> (parens $ lambda _args (tuple $ _jvars:_care'))) <> comma <+>
                              (pp "|" <> tuple [_jvars, _vars, tuple _care'] <> pp "|" <+> (tuple $ _jvars':_vars'))))
                     -- <pref>.antijoin(<rname>.filter(<filters>).map(|<args>|<jvars>)).map(|(<jvars>, <vars>)|(<jvars'>, <vars'>))
                     (pref <> pp "." <> pp "antijoin" <> 
                              (parens $ pp rname <> _filters <> pp "." <> pp "map" <> (parens $ lambda _args _jvars)) <>
                              pp "." <> pp "map" <> 
                              (parens $ lambda (tuple [_jvars, _vars]) (tuple $ _jvars': _vars'))))

lambda :: Doc -> Doc -> Doc
lambda as e = pp "|" <> as <> pp "|" <+> e

mkFilter :: (?s::DFSession) => Expr -> Expr -> Doc
mkFilter e pat | pat' == pp "_" = empty
               | otherwise = pp "match" <+> mkExpr e <+> 
                             pp "{" <> pat' <+> pp "=>" <+> pp "true" <> comma <+> pp "_" <+> pp "=>" <+> pp "false" <> pp "}"
    where pat' = mkFilter' pat

mkFilter' :: (?s::DFSession) => Expr -> Doc
mkFilter' (EVar _) = pp "_"
mkFilter' (EStruct c as) | length structCons == 1 && (all (== pp "_") afs) = pp "_"
                         | otherwise = pp structName <> pp "::" <> pp c <> as'
    where Struct{..} = getStruct (dfQ ?s) c 
          args = consArgs $ getConstructor (dfQ ?s) c
          afs = map mkFilter' as
          as' = case as of
                     [] -> empty
                     _  -> pp "{" <> (commaSep $ map (\(arg, a) -> pp (name arg) <> pp ":" <+> a) 
                                               $ zip args afs) <> pp "}"
mkFilter' e = error $ "Dataflog.mkFilter' " ++ show e

mkExpr :: (?s::DFSession) => Expr -> Doc
mkExpr (EVar v)             = pp v
mkExpr (EApply f as)        = pp f <> (parens $ commaSep $ map mkExpr as)
mkExpr (EField _ s f)       = mkExpr s <> pp "." <> pp f
mkExpr (EBool True)         = pp "true"
mkExpr (EBool False)        = pp "false"
mkExpr (EBit w i) | w<=64   = pp i
                  | otherwise = mkExpr $ EInt i
mkExpr (EInt i)             = pp "BigUint::parse_bytes" <> 
                              (parens $ pp "b\"" <> pp i <> pp "\"" <> comma <+> pp "10") <> pp ".unwrap()"
mkExpr (EString s)          = pp $ "\"" ++ s ++ "\""
mkExpr (EStruct c as)       = (pp $ name s) <> pp "::" <> pp c <> pp "{"  <> 
                              (commaSep $ map (\(arg, a) -> (pp $ name arg) <> pp ":" <+> mkExpr a) $ zip args as) <> pp "}"
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
         Concat -> error "not implemented: Dataflog.mkExpr Concat"
         Impl   -> mkExpr $ EBinOp Or (EUnOp Not e1) e2
    where f o = parens $ mkExpr e1 <+> pp o <+> mkExpr e2

mkExpr (EUnOp Not e)        = parens $ pp "!" <> mkExpr e
mkExpr (ESlice e h l)       = let e' = mkExpr e
                                  e1 = if' (l == 0) e' (parens $ e' <+> pp ">>" <+> pp l)
                                  mask = foldl' setBit 0 [0..(h-l)]
                                  mask' = mkExpr $ EBit (h-l+1) mask
                              in parens $ e1 <+> pp "&" <+> mask'
mkExpr (ECond [] d)         = mkExpr d
mkExpr (ECond ((c,e):cs) d) = pp "if" <+> mkExpr c <+> pp "{" <> mkExpr e <> pp "}" <+> 
                              pp "else" <+> (mkExpr $ ECond cs d)
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
    f = pp "." <> pp "filter" <> (parens $ pp "|" <> (tuple $ _jvars:_vars) <> pp "|" <+> _conds)
    pref' = pref <> f
