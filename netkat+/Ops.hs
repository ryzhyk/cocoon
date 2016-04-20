module Ops where

import Text.PrettyPrint

import PP

data BOp = Eq
         | Lt
         | Gt
         | Lte
         | Gte
         | And
         | Or
         | Impl
         | Plus
         | Minus
         | Mod
         deriving (Eq)

instance PP BOp where
    pp Eq     = pp "=="
    pp Lt     = pp "<"
    pp Gt     = pp ">"
    pp Lte    = pp "<="
    pp Gte    = pp ">="
    pp And    = pp "and"
    pp Or     = pp "or"
    pp Impl   = pp "=>"
    pp Plus   = pp "+"
    pp Minus  = pp "-"
    pp Mod    = pp "%"

instance Show BOp where
    show = render . pp

data UOp = Not
           deriving (Eq)

instance PP UOp where
    pp Not = pp "not"

instance Show UOp where
    show = render . pp
