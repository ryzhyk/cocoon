module Ops where

data BOp = Eq
         | Lt
         | Gt
         | Lte
         | Gte
         | And
         | Or
         | Plus
         | Minus
         | Mod
         deriving (Eq)

data UOp = Not
           deriving (Eq)
