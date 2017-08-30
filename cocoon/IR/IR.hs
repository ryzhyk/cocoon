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

{-# LANGUAGE ImplicitParams, OverloadedStrings, RecordWildCards, TupleSections, LambdaCase #-}

module IR.IR where
 
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G 
import qualified Data.GraphViz        as G
import Text.PrettyPrint
import Data.Text.Lazy(Text, unpack)
import Data.List
import Data.Maybe
import Control.Monad
import Data.Functor.Identity
--import Debug.Trace

import Util
import Ops
import PP

type NodeId    = G.Node
type VarName   = String
type RelName   = String
type ColName   = String
type FieldName = String

data Type = TBool
          | TBit Int
          deriving (Eq)

typeWidth :: Type -> Int
typeWidth TBool    = 1
typeWidth (TBit w) = w

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

data Expr = EPktField {exprFieldName :: FieldName, exprType :: Type}
          | EVar      {exprVarName :: VarName, exprType :: Type}
          | ECol      {exprColName :: ColName, exprType :: Type}
          | ESlice    {exprArg :: Expr, exprH :: Int, exprL :: Int}
          | EBool     {exprBoolVal :: Bool}
          | EBit      {exprWidth :: Int, exprIntVal :: Integer}
          | EBinOp    {exprBOp :: BOp, exprArg1 :: Expr, exprArg2 :: Expr}
          | EUnOp     {exprUOp :: UOp, exprArg :: Expr}
          deriving (Eq)

instance PP Expr where
    pp (EPktField f _)   = "pkt." <> pp f
    pp (EVar v _)        = pp v
    pp (ECol col _)      = "." <> pp col
    pp (ESlice e h l)    = pp e <> "[" <> pp h <> ":" <> pp l <> "]"
    pp (EBool True)      = "true" 
    pp (EBool False)     = "false" 
    pp (EBit w v)        = pp w <> "'d" <> pp v
    pp (EBinOp op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (EUnOp op e)      = parens $ pp op <+> pp e

instance Show Expr where
    show = render . pp

exprMap :: (Expr -> Expr) -> Expr -> Expr
exprMap f e@EPktField{}       = f e
exprMap f e@EVar{}            = f e
exprMap f e@ECol{}            = f e
exprMap f   (ESlice e h l)    = f $ ESlice (exprMap f e) h l
exprMap f e@EBool{}           = f e
exprMap f e@EBit{}            = f e
exprMap f   (EBinOp op e1 e2) = f $ EBinOp op (exprMap f e1) (exprMap f e2)
exprMap f   (EUnOp op e)      = f $ EUnOp op $ exprMap f e

exprVars :: Expr -> [VarName]
exprVars e = nub $ exprVars' e

exprVars' (EPktField _ _)   = []
exprVars' (EVar v _)        = [v]
exprVars' (ECol _ _)        = []
exprVars' (ESlice e _ _)    = exprVars' e
exprVars' (EBool _)         = []
exprVars' (EBit _ _)        = []
exprVars' (EBinOp _ e1 e2)  = exprVars' e1 ++ exprVars' e2
exprVars' (EUnOp _ e)       = exprVars' e

exprAtoms :: Expr -> [Expr]
exprAtoms e = nub $ exprAtoms' e

exprAtoms' e@EPktField{}      = [e]
exprAtoms' e@EVar{}           = [e]
exprAtoms' e@ECol{}           = [e]
exprAtoms'   (ESlice e _ _)   = exprAtoms' e
exprAtoms'   EBool{}          = []
exprAtoms'   EBit{}           = []
exprAtoms'   (EBinOp _ e1 e2) = exprAtoms' e1 ++ exprAtoms' e2
exprAtoms'   (EUnOp _ e)      = exprAtoms' e

exprSubstVar :: VarName -> Expr -> Expr -> Expr
exprSubstVar v e' e = exprMap (\case 
                                EVar v' _ | v' == v -> e'
                                x                   -> x) e


cfgSubstVar :: VarName -> Expr -> CFG -> CFG
cfgSubstVar v e cfg = cfgMapCtx g f cfg
    where
    g :: NodeId -> Node -> Node 
    -- only Cond and Par nodes occur in filter expressions
    g _   Cond{..} = Cond $ map (\(c,b) -> (exprSubstVar v e c, b)) nodeConds
    g _ n@Par{}    = n
    g _ n          = error $ "IR.cfgSubstVar g " ++ show n
    f :: CFGCtx -> Maybe Action
    f ctx = case ctxAction cfg ctx of
                 ASet     l r  -> Just $ ASet (exprSubstVar v e l) (exprSubstVar v e r)
                 APut     t es -> Just $ APut t (map (exprSubstVar v e) es)
                 ADelete  t c  -> Just $ ADelete t $ exprSubstVar v e c

plSubstVar :: VarName -> Expr -> Pipeline -> Pipeline
plSubstVar v e pl = pl{plCFG = cfgSubstVar v e (plCFG pl)}

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


type Record = M.Map ColName Expr

-- Database delta: maps relation name into a set of facts with polarities.
type Delta = M.Map RelName [(Bool, Record)]

-- Database snapshot
type DB    = M.Map RelName [Record]

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

actionRHSVars :: Action -> [VarName]
actionRHSVars (ASet _ e2)   = exprVars e2
actionRHSVars (APut _ vs)   = nub $ concatMap exprVars vs
actionRHSVars (ADelete _ c) = exprVars c

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

cfgDump :: CFG -> FilePath -> IO ()
cfgDump cfg f = writeFile f $ unpack $ cfgToDot cfg

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

cfgMapCtxM :: (Monad m) => (NodeId -> Node -> m Node) -> (CFGCtx -> m (Maybe Action)) -> CFG -> m CFG
cfgMapCtxM g f cfg = foldM (nodeMapCtxM g f) cfg $ G.nodes cfg

cfgMapCtx :: (NodeId -> Node -> Node) -> (CFGCtx -> (Maybe Action)) -> CFG -> CFG
cfgMapCtx g f cfg = runIdentity $ cfgMapCtxM (\nd node -> return $ g nd node) (\ctx -> return $ f ctx) cfg

nodeMapCtxM :: (Monad m) => (NodeId -> Node -> m Node) -> (CFGCtx -> m (Maybe Action)) -> CFG -> G.Node -> m CFG
nodeMapCtxM g f cfg nd = do
    let (Just (pre, _, node, suc), cfg_) = G.match nd cfg
    node' <- g nd node
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

ctxRHSVars :: CFG -> CFGCtx -> [VarName]
ctxRHSVars cfg (CtxNode nd) =  
    case node of
         Fork{}   -> nodeDeps node
         Lookup{} -> nodeDeps node
         Cond{}   -> nub $ concatMap (exprVars . fst) $ nodeConds node
         Par{}    -> []
     where node = fromJust $ G.lab cfg nd
ctxRHSVars cfg ctx = actionRHSVars $ ctxAction cfg ctx

ctxAssignsFullVar :: CFG -> VarName -> CFGCtx -> Bool
ctxAssignsFullVar _ _ CtxNode{} = False
ctxAssignsFullVar cfg v ctx     = case ctxAction cfg ctx of
                                       ASet (EVar v' _) _ | v' == v -> True
                                       _                            -> False

ctxLiveVars :: Pipeline -> CFGCtx -> [VarName]
ctxLiveVars Pipeline{..} ctx = filter live $ M.keys plVars
    where 
    -- forward search for locations that use the variable, aborting when the variable is assigned
    live var = not $ null $ ctxSearchForward plCFG ctx (elem var . ctxRHSVars plCFG) (ctxAssignsFullVar plCFG var)
