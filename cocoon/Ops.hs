{-
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

{-# LANGUAGE OverloadedStrings #-}

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
    pp Eq     = "=="
    pp Neq    = "!="
    pp Lt     = "<"
    pp Gt     = ">"
    pp Lte    = "<="
    pp Gte    = ">="
    pp And    = "and"
    pp Or     = "or"
    pp Impl   = "=>"
    pp Plus   = "+"
    pp Minus  = "-"
    pp Mod    = "%"
    pp ShiftR = ">>"
    pp ShiftL = "<<"
    pp Concat = "++"

instance Show BOp where
    show = render . pp

data UOp = Not
           deriving (Eq)

instance PP UOp where
    pp Not = "not"

instance Show UOp where
    show = render . pp
