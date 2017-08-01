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

{-# LANGUAGE ImplicitParams, OverloadedStrings, RecordWildCards #-}

module IR where
 
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G 
import qualified Data.GraphViz        as G
import Text.PrettyPrint
import Data.Text.Lazy(Text)
import Data.List

import Util
import Ops
import PP

type NodeId  = G.Node
type VarName = String
type RelName = String
type ColName = String

data Type = TBool
          | TBit Int
          deriving (Eq)

instance PP Type where 
    pp TBool    = "bool"
    pp (TBit w) = "bit<" <> pp w <> ">"

instance Show Type where
    show = render . pp

data Var = Var VarName NodeId Type deriving (Eq)

instance PP Var where
    pp (Var n nid t) = pp n <> "@" <> pp nid <> ":" <+> pp t

instance Show Var where
    show = render . pp

-- data Relation = Relation RelName [Var]

data Expr = EPktField String
          | EVar      VarName
          | ECol      ColName
          | ESlice    Expr Int Int
          | EBool     Bool
          | EBit      Int Integer
          | EBinOp    BOp Expr Expr
          | EUnOp     UOp Expr
          deriving (Eq)

instance PP Expr where
    pp (EPktField f)     = "pkt." <> pp f
    pp (EVar v)          = pp v
    pp (ECol col)        = "." <> pp col
    pp (ESlice e h l)    = pp e <> "[" <> pp h <> ":" <> pp l <> "]"
    pp (EBool True)      = "true" 
    pp (EBool False)     = "false" 
    pp (EBit w v)        = pp w <> "'d" <> pp v
    pp (EBinOp op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp op e)      = parens $ pp op <+> pp e

instance Show Expr where
    show = render . pp

exprVars :: Expr -> [VarName]
exprVars e = nub $ exprVars' e

exprVars' (EPktField _)     = []
exprVars' (EVar v)          = [v]
exprVars' (ECol _)          = []
exprVars' (ESlice e _ _)    = exprVars' e
exprVars' (EBool _)         = []
exprVars' (EBit _ _)        = []
exprVars' (EBinOp _ e1 e2)  = exprVars' e1 ++ exprVars' e2
exprVars' (EUnOp _ e)       = exprVars' e

conj :: [Expr] -> Expr
conj = conj' . filter (/= EBool True)

conj' :: [Expr] -> Expr
conj' []     = EBool True
conj' [e]    = e
conj' (e:es) = EBinOp And e (conj' es)

disj :: [Expr] -> Expr
disj = disj' . filter (/= EBool False)

disj' :: [Expr] -> Expr
disj' []     = EBool False
disj' [e]    = e
disj' (e:es) = EBinOp Or e (disj' es)

data Action = ASet     Expr Expr
            | APut     String [Expr]
            | ADelete  String Expr
            {-| ABuiltin String [Expr] -}

instance PP Action where
    pp (ASet e1 e2)  = pp e1 <+> ":=" <+> pp e2
    pp (APut t vs)   = pp t <> ".put" <> (parens $ hsep $ punctuate comma $ map pp vs)
    pp (ADelete t c) = pp t <> ".delete" <> (parens $ pp c)

instance Show Action where
    show = render . pp

actionVars :: Action -> [VarName]
actionVars (ASet e1 e2)  = nub $ exprVars e1 ++ exprVars e2
actionVars (APut _ vs)   = nub $ concatMap exprVars vs
actionVars (ADelete _ e) = exprVars e

-- Next action descriptor
data Next = Goto NodeId
          | Send Expr
          | Drop
          deriving(Eq)

instance PP Next where
    pp (Goto nid) = "goto" <+> pp nid
    pp (Send p)   = "send" <+> pp p
    pp Drop       = "drop"

instance Show Next where
    show = render . pp

-- Basic block
data BB = BB [Action] Next

instance PP BB where
    pp (BB as nxt) = vcat $ (map ((<> ";") . pp) as) ++ [pp nxt]

instance Show BB where 
    show = render . pp

bbVars :: BB -> [VarName]
bbVars (BB as _) = nub $ concatMap actionVars as

data Node = Fork   RelName [VarName] BB     -- list of vars fork condition depends on (prevents these var from being optimized away)
          | Lookup RelName [VarName] BB BB
          | Cond   [(Expr, BB)]
          | Par    [BB]

mapBB :: (BB -> BB) -> Node -> Node
mapBB f (Fork r vs bb)        = Fork r vs $ f bb
mapBB f (Lookup r vs bb1 bb2) = Lookup r vs (f bb1) (f bb2)
mapBB f (Cond cs)             = Cond $ map (mapSnd f) cs
mapBB f (Par bs)              = Par $ map f bs

nodeVars :: Node -> [VarName]
nodeVars (Fork _ vs b)       = nub $ vs ++ bbVars b
nodeVars (Lookup _ vs b1 b2) = nub $ vs ++ bbVars b1 ++ bbVars b2
nodeVars (Cond cs)           = nub $ concatMap (\(c,b) -> exprVars c ++ bbVars b) cs 
nodeVars (Par bs)            = nub $ concatMap bbVars bs

instance PP Node where 
    pp (Fork t vs b)       = ("fork(" <> pp t <> ")[" <> (hsep $ punctuate comma $ map pp vs) <> "]") $$ (nest' $ pp b)
    pp (Lookup t vs th el) = ("lookup(" <> pp t <> ")[" <> (hsep $ punctuate comma $ map pp vs) <> "]") $$ (nest' $ pp th) $$ "default" $$ (nest' $ pp el)
    pp (Cond cs)           = "cond" $$ (vcat $ map (\(c,b) -> (nest' $ pp c <> ":" <+> pp b)) cs)
    pp (Par bs)            = "par" $$ (vcat $ map (\b -> (nest' $ ":" <+> pp b)) bs)

instance Show Node where
    show = render . pp 

instance G.Labellable Node where
    toLabelValue = G.toLabelValue . show

data Edge = Edge deriving (Eq)

instance G.Labellable Edge where
    toLabelValue _ = G.toLabelValue $ (""::String)

-- DAG
type CFG = G.Gr Node Edge

data Pipeline = Pipeline {plVars :: Vars, plCFG :: CFG, plEntryNode :: NodeId}

type Vars = M.Map VarName Type

cfgToDot :: CFG -> Text
cfgToDot cfg = G.printDotGraph $ G.graphToDot G.quickParams cfg

-- Node metadata relates pipeline nodes to 
-- original program locations
--data NodeMeta = NodeMeta C.ECtx C.Expr
--type Meta = M.Map NodeId NodeMeta

