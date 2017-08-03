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

{-# LANGUAGE ImplicitParams, OverloadedStrings, RecordWildCards, TupleSections #-}

module IR where
 
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G 
import qualified Data.GraphViz        as G
import Text.PrettyPrint
import Data.Text.Lazy(Text)
import Data.List
import Data.Maybe
import Control.Monad
--import Debug.Trace

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
data BB = BB {bbActions :: [Action], bbNext :: Next}

instance PP BB where
    pp (BB as nxt) = vcat $ (map ((<> ";") . pp) as) ++ [pp nxt]

instance Show BB where 
    show = render . pp

bbVars :: BB -> [VarName]
bbVars (BB as _) = nub $ concatMap actionVars as

data Node = Fork   {nodeRel :: RelName, nodeDeps :: [VarName], nodePL :: Pipeline, nodeBB::BB}  -- list of vars fork condition depends on (prevents these var from being optimized away)
          | Lookup {nodeRel :: RelName, nodeDeps :: [VarName], nodePL :: Pipeline, nodeThen :: BB, nodeElse :: BB}
          | Cond   {nodeConds :: [(Expr, BB)]}
          | Par    {nodeBBs :: [BB]}

mapBB :: (BB -> BB) -> Node -> Node
mapBB f (Fork r vs pl bb)        = Fork r vs pl $ f bb
mapBB f (Lookup r vs pl bb1 bb2) = Lookup r vs pl (f bb1) (f bb2)
mapBB f (Cond cs)                = Cond $ map (mapSnd f) cs
mapBB f (Par bs)                 = Par $ map f bs

nodeVars :: Node -> [VarName]
nodeVars (Fork _ vs _ b)       = nub $ vs ++ bbVars b
nodeVars (Lookup _ vs _ b1 b2) = nub $ vs ++ bbVars b1 ++ bbVars b2
nodeVars (Cond cs)             = nub $ concatMap (\(c,b) -> exprVars c ++ bbVars b) cs 
nodeVars (Par bs)              = nub $ concatMap bbVars bs

instance PP Node where 
    pp (Fork t vs _ b)       = ("fork(" <> pp t <> ")[" <> (hsep $ punctuate comma $ map pp vs) <> "]") $$ (nest' $ pp b)
    pp (Lookup t vs _ th el) = ("lookup(" <> pp t <> ")[" <> (hsep $ punctuate comma $ map pp vs) <> "]") $$ (nest' $ pp th) $$ "default" $$ (nest' $ pp el)
    pp (Cond cs)             = "cond" $$ (vcat $ map (\(c,b) -> (nest' $ pp c <> ":" <+> pp b)) cs)
    pp (Par bs)              = "par" $$ (vcat $ map (\b -> (nest' $ ":" <+> pp b)) bs)

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

-- CFG context identifies location within a CFG
data CFGCtx = CtxNode       {ctxNode :: NodeId}
            | CtxFork       {ctxNode :: NodeId, ctxAct :: Int}
            | CtxLookupThen {ctxNode :: NodeId, ctxAct :: Int}
            | CtxLookupDef  {ctxNode :: NodeId, ctxAct :: Int}
            | CtxCond       {ctxNode :: NodeId, ctxCond :: Int, ctxAct :: Int}
            | CtxPar        {ctxNode :: NodeId, ctxBB :: Int, ctxAct :: Int}
            deriving (Eq, Show)

ctxSuc :: CFG -> CFGCtx -> [CFGCtx]
ctxSuc cfg ctx =
    case ctx of
         CtxNode       nd ->
             case node of 
                  Fork _ _ _ b     -> bbEntry (CtxFork nd) b
                  Lookup _ _ _ t e -> nub $ bbEntry (CtxLookupThen nd) t ++ bbEntry (CtxLookupDef nd) e
                  Cond cs          -> nub $ concat $ mapIdx (\(_, b) i -> bbEntry (CtxCond nd i) b) cs
                  Par bs           -> nub $ concat $ mapIdx (\b i -> bbEntry (CtxPar nd i) b) bs
         CtxFork       nd a   | (a+1) < (length $ bbActions $ nodeBB node)                 -> [CtxFork nd (a+1)]
                              | otherwise                                                  -> bbSuc $ nodeBB node
         CtxLookupThen nd a   | (a+1) < (length $ bbActions $ nodeThen node)               -> [CtxLookupThen nd (a+1)]
                              | otherwise                                                  -> bbSuc $ nodeThen node
         CtxLookupDef  nd a   | (a+1) < (length $ bbActions $ nodeElse node)               -> [CtxLookupDef nd (a+1)]
                              | otherwise                                                  -> bbSuc $ nodeElse node
         CtxCond       nd c a | (a+1) < (length $ bbActions $ (snd $ nodeConds node !! c)) -> [CtxCond nd c (a+1)]
                              | otherwise                                                  -> bbSuc (snd $ nodeConds node !! c)
         CtxPar        nd b a | (a+1) < (length $ bbActions $ (nodeBBs node !! b))         -> [CtxPar nd b (a+1)]
                              | otherwise                                                  -> bbSuc (nodeBBs node !! b)
    where node = fromJust $ G.lab cfg $ ctxNode ctx

bbSuc :: BB -> [CFGCtx]
bbSuc (BB _ (Goto nd)) = [CtxNode nd]
bbSuc _                = []

bbEntry :: (Int -> CFGCtx) -> BB -> [CFGCtx]
bbEntry f bb | length (bbActions bb) > 0 = [f 0]
             | otherwise                 = bbSuc bb

ctxPre :: CFG -> CFGCtx -> [CFGCtx]
ctxPre cfg ctx =
    case ctx of
         CtxNode       nd                     -> nodePre cfg nd
         CtxFork       nd a   | a > 0         -> [CtxFork nd (a-1)]
         CtxLookupThen nd a   | a > 0         -> [CtxLookupThen nd (a-1)]
         CtxLookupDef  nd a   | a > 0         -> [CtxLookupDef nd (a-1)]
         CtxCond       nd c a | a > 0         -> [CtxCond nd c (a-1)]
         CtxPar        nd b a | a > 0         -> [CtxPar nd b (a-1)]
         _                                    -> [CtxNode $ ctxNode ctx]

nodePre :: CFG -> NodeId -> [CFGCtx]
nodePre cfg nd = nub $ concatMap nodePre' $ G.pre cfg nd
    where nodePre' :: G.Node -> [CFGCtx]
          nodePre' nd' = case fromJust $ G.lab cfg nd' of
                              Fork _ _ _ b     -> bbExit nd' (CtxFork nd') b
                              Lookup _ _ _ t e -> nub $ (if bbNext t == Goto nd then bbExit nd' (CtxLookupThen nd') t else []) ++ 
                                                        (if bbNext e == Goto nd then bbExit nd' (CtxLookupDef nd') e else [])
                              Cond cs          -> nub $ concat $ mapIdx (\(_, b) i -> if bbNext b == Goto nd then bbExit nd' (CtxCond nd' i) b else []) cs
                              Par bs           -> nub $ concat $ mapIdx (\b i -> if bbNext b == Goto nd then bbExit nd' (CtxPar nd' i) b else []) bs

bbExit :: NodeId -> (Int -> CFGCtx) -> BB -> [CFGCtx]
bbExit nd f (BB as _) | length as > 0 = [f $ length as - 1]
                      | otherwise     = [CtxNode nd]

-- match - add context to result set and stop following the branch
-- abort - stop following the branch
ctxSearchForward :: CFG -> CFGCtx -> (CFGCtx -> Bool) -> (CFGCtx -> Bool) -> [CFGCtx]
ctxSearchForward cfg ctx match abort = ctxSearchForward' [] (ctxSuc cfg ctx)
    where
    ctxSearchForward' :: [CFGCtx] -> [CFGCtx] -> [CFGCtx]
    ctxSearchForward' _ [] = []
    ctxSearchForward' explored front = {-trace ("ctxSearchForward' " ++ show front) $-} matches ++ ctxSearchForward' (explored ++ front) front''
        where (matches, front') = partition match front
              rest = filter (not . abort) front'
              front'' = (nub $ concatMap (ctxSuc cfg) rest) \\ explored

ctxSearchBackward :: CFG -> CFGCtx -> (CFGCtx -> Bool) -> (CFGCtx -> Bool) -> [CFGCtx]
ctxSearchBackward cfg ctx match abort = ctxSearchBackward' [] (ctxPre cfg ctx)
    where
    ctxSearchBackward' :: [CFGCtx] -> [CFGCtx] -> [CFGCtx]
    ctxSearchBackward' _ [] = []
    ctxSearchBackward' explored front = matches ++ ctxSearchBackward' (explored ++ front) front''
        where front' = filter (not . abort) front
              (matches, rest) = partition match front'
              front'' = (nub $ concatMap (ctxPre cfg) rest) \\ explored

ctxAction :: CFG -> CFGCtx -> Action
ctxAction cfg ctx = 
    case ctx of 
         CtxNode       _     -> error "IR.ctxAction CtxNode"
         CtxFork       _ a   -> (bbActions $ nodeBB node) !! a
         CtxLookupThen _ a   -> (bbActions $ nodeThen node) !! a
         CtxLookupDef  _ a   -> (bbActions $ nodeElse node) !! a
         CtxCond       _ c a -> (bbActions $ snd $ (nodeConds node) !! c) !! a
         CtxPar        _ b a -> (bbActions $ (nodeBBs node) !! b) !! a
    where node = fromJust $ G.lab cfg $ ctxNode ctx

cfgMapCtxM :: (Monad m) => (NodeId -> Node -> Node) -> (CFGCtx -> m (Maybe Action)) -> CFG -> m CFG
cfgMapCtxM g f cfg = foldM (nodeMapCtxM g f) cfg $ G.nodes cfg

nodeMapCtxM :: (Monad m) => (NodeId -> Node -> Node) -> (CFGCtx -> m (Maybe Action)) -> CFG -> G.Node -> m CFG
nodeMapCtxM g f cfg nd = do
    let (Just (pre, _, node, suc), cfg_) = G.match nd cfg
        node' = g nd node
    node'' <- case node' of
                   Fork t vs pl b       -> (liftM $ Fork t vs pl) $ bbMapCtxM f (CtxFork nd) b
                   Lookup t vs pl th el -> (liftM2 $ Lookup t vs pl) (bbMapCtxM f (CtxLookupThen nd) th) (bbMapCtxM f (CtxLookupDef nd) el)
                   Cond cs              -> liftM Cond $ mapIdxM (\(c,b) i -> liftM (c,) $ bbMapCtxM f (CtxCond nd i) b) cs
                   Par bs               -> liftM Par $ mapIdxM (\b i -> bbMapCtxM f (CtxPar nd i) b) bs
    return $ (pre, nd, node'', suc) G.& cfg_

bbMapCtxM :: (Monad m) => (CFGCtx -> m (Maybe Action)) -> (Int -> CFGCtx) -> BB -> m BB
bbMapCtxM f fctx (BB as nxt) = do
    as' <- (liftM catMaybes) $ mapIdxM (\_ i -> f (fctx i)) as
    return $ BB as' nxt
    

-- Node metadata relates pipeline nodes to 
-- original program locations
--data NodeMeta = NodeMeta C.ECtx C.Expr
--type Meta = M.Map NodeId NodeMeta

