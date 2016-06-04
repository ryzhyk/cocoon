{-# LANGUAGE ImplicitParams #-}

module Boogie.BoogieHelpers where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import qualified Data.Map as M

import Type
import PP
import Syntax
import Pos
import Name

outputTypeName = "_Output"
locTypeName    = "_Location"

outputVar = "_outp"
depthVar  = "_depth"
locationVar = "_loc"


-- Set of modified fields. Includes expressions of the form pkt.f1.f2.....fn
type MSet = [(Expr, Doc)]
type Locals = M.Map String Doc

msetEq :: MSet -> MSet -> Bool
msetEq ms1 ms2 = length ms1 == length ms2 && (length $ intersect (map fst ms1) (map fst ms2)) == length ms1

-- assumes non-overlapping sets
msetUnion :: MSet -> MSet -> MSet
msetUnion s1 s2 = s1 ++ s2

overlapsMSet :: (?r::Refine) => ECtx -> Expr -> MSet -> Bool
overlapsMSet ctx x mset = (isJust $ lookup x mset) ||
                          case typ' ?r ctx x of
                               TStruct _ fs -> any (\f -> overlapsMSet ctx (EField nopos x $ name f) mset) fs
                               _            -> False 

-- Boogie syntax helpers

(.:=) :: Doc -> Doc -> Doc
(.:=) l r = l <+> text ":=" <+> r <> semi

var :: Doc -> Doc -> Doc
var n t = pp "var" <+> n <> colon <+> t <> semi

modifies :: Doc -> Doc
modifies v = pp "modifies" <+> v <> semi

assrt :: Doc -> Doc
assrt c = if c == pp "true" then empty else pp "assert" <+> c <> semi

assume :: Doc -> Doc
assume c = if c == pp "true" then empty else pp "assume" <+> c <> semi

(.==) :: Doc -> Doc -> Doc
(.==) x y = parens $ x <+> pp "==" <+> y

(.!=) :: Doc -> Doc -> Doc
(.!=) x y = parens $ x <+> pp "!=" <+> y

(.||) :: Doc -> Doc -> Doc
(.||) x y = parens $ x <+> pp "||" <+> y

(.&&) :: Doc -> Doc -> Doc
(.&&) x y = parens $ x <+> pp "&&" <+> y

($&&) :: Doc -> Doc -> Doc
($&&) x y = (lparen <> x <+> pp "&&")
            $$ 
            y <> rparen

(.=>) :: Doc -> Doc -> Doc
(.=>) x y = parens $ x <+> pp "==>" <+> y

(.<) :: Doc -> Doc -> Doc
(.<) x y = parens $ x <+> pp "<" <+> y

(.>) :: Doc -> Doc -> Doc
(.>) x y = parens $ x <+> pp ">" <+> y

(.<=) :: Doc -> Doc -> Doc
(.<=) x y = parens $ x <+> pp "<=" <+> y

(.>=) :: Doc -> Doc -> Doc
(.>=) x y = parens $ x <+> pp ">=" <+> y

(.+) :: Doc -> Doc -> Doc
(.+) x y = parens $ x <+> pp "+" <+> y

(.-) :: Doc -> Doc -> Doc
(.-) x y = parens $ x <+> pp "-" <+> y

(.*) :: Doc -> Doc -> Doc
(.*) x y = parens $ x <+> pp "*" <+> y

(.:) :: Doc -> Doc -> Doc
(.:) x y = x <> colon <+> y

apply :: String -> [Doc] -> Doc
apply f as = pp f <> (parens $ hsep $ punctuate comma as)

exists :: [Doc] -> Doc -> Doc
exists args e = pp "exists" <+> (hsep $ punctuate (pp ",") args) <+> pp "::" <> lparen $$ (nest' e) $$ rparen

axiom :: [Doc] -> Doc -> Doc
axiom [] e = pp "axiom" <+> (parens e) <> semi
axiom vs e = pp "axiom" <+> (parens $ pp "forall" <+> args <+> pp "::" <+> e) <> semi
    where args = hsep $ punctuate comma vs

call :: String -> [Doc] -> Doc
call f as = pp "call" <+> apply f as <> semi

havoc :: Doc -> Doc
havoc x = pp "havoc" <+> x <> semi

havoc' :: Refine -> (Doc, Type) -> Doc
havoc' r (x,t) = havoc x
                 $$
                 (assume $ checkBVBounds r [(x,t)])

ret :: Doc
ret = pp "return" <> semi

ite :: Doc -> Doc -> Doc -> Doc
ite c t e = (pp "if" <+> parens c <+> pp "then" <+> lparen)
            $$
            (nest' t)
            $$
            (rparen <+> pp "else" <+> lparen)
            $$
            (nest' e)
            $$
            rparen

checkBVBounds :: Refine -> [(Doc, Type)] -> Doc
checkBVBounds r xs = if null cs then pp "true" else (hsep $ intersperse (pp "&&") cs)
    where cs = concatMap (\(v, x) -> case typ' r undefined x of
                                          TUInt _ w   -> [apply ("checkBounds" ++ show w) [v]]
                                          TStruct _ _ -> let TUser _ sname = typ'' r undefined x in
                                                         [apply ("checkBounds" ++ sname) [v]]
                                          _           -> []) xs


