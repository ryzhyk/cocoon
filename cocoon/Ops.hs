module Ops where

import Text.PrettyPrint

import PP

data BOp = Eq
         | Neq
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
         | ShiftR
         | ShiftL
         | Concat
         deriving (Eq)

instance PP BOp where
    pp Eq     = pp "=="
    pp Neq    = pp "!="
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
    pp ShiftR = pp ">>"
    pp ShiftL = pp "<<"
    pp Concat = pp "++"

instance Show BOp where
    show = render . pp

data UOp = Not
           deriving (Eq)

instance PP UOp where
    pp Not = pp "not"

instance Show UOp where
    show = render . pp
