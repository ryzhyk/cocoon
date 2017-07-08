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

-- Intemediate representation for dataplane languages like OpenFlow and P4

{-# LANGUAGE ImplicitParams #-}

module IR () where
 
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G 

import qualified Syntax as C

type NodeId  = G.Node
type VarName = String
type RelName = String
type ColName = String

data Type = TBool
          | TBit Int Integer

data Var = Var VarName NodeId Type

data Relation = Relation RelName [Var]

data Expr = EPktField String
          | EVar      VarName
          | ECol      ColName
          | ESlice    Expr Int Int
          | EBool     Bool
          | EBit      Int Integer
          | EBinOp    BOp Expr Expr
          | EUnOp     UOp Expr

data Action = ASet     Expr Expr
            | APut     String [Expr]
            | ADelete  String Expr
            {-| ABuiltin String [Expr] -}

-- Next action descriptor
data Next = Goto NodeId
          | Send Expr
          | Drop

-- Basic block
newtype BB = BB [Action] Next

data Node = Fork   RelName Expr BB
          | Lookup RelName Expr BB BB
          | Cond   [(Expr, BB)]
          | Par    [BB]

-- DAG
type CFG = G.Gr Node ()

data Pipeline = Pipeline Vars CFG NodeId

type Vars = M.Map VarName (NodeId, Type)

-- Node metadata relates pipeline nodes to 
-- original program locations
--data NodeMeta = NodeMeta C.ECtx C.Expr
--type Meta = M.Map NodeId NodeMeta

-- Optimizations: 
--     * eliminate unused variables (for example only a few vars
--       returned by a query are used)
--     * variable elimination by substitution
--     * merging tables to eliminate some variables
--     * merge cascade of conditions
--     * merge sequence of basic blocks
--     * merge cascades of parallel blocks
