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

{-# LANGUAGE ImplicitParams #-}

module Compile2IR () where

import Data.Maybe
import qualified Data.Map as M
 
import Syntax
import qualified IR as I

type CompileState a = State I.Pipeline a

compilePort :: Refine -> Role -> I.Pipeline
compilePort r role@Role{..} = let ?r = r in fst $ execState (compilePort' role) (I.Pipeline M.empty G.empty 0)

compilePort' :: Role -> CompileState ()
compilePort' role = do 
    entrynd <- allocNode
    setEntryNode entrynd
    let e = expr2Statement r (CtxRole role) roleBody
    let rel = getRelation ?r roleTable
    (vars, asns) <- declAsnVar M.empty roleKey relRecordType entrynd $ relCols rel
    c <- I.EBinOp (I.ECol "portnum") (I.EPktField "portnum")
    (entryndb, _) <- compileExpr vars (CtxRole role) Nothing e
    updateNode entrynd (I.Lookup (name rel) c (I.BB asns $ I.Goto entryndb) (I.BB [] I.Drop)) [entryndb]
    -- TODO: optimize 


compileExpr :: (MonadError String me, ?r::Refine) => M.Map String String -> ECtx -> Maybe I.NodeId -> Expr -> CompileState (M.Map String String, I.NodeId)
compileExpr vars ctx exitnd e = do
    entrynd <- allocNode
    vars' <- compileExprAt vars ctx entrynd exitnd e
    return (entrynd, vars')

compileExprAt :: (MonadError String me, ?r::Refine) => M.Map String String -> ECtx -> I.NodeId -> Maybe I.NodeId -> Expr -> CompileState (M.Map String String)
compileExprAt vars ctx entrynd exitnd (E e@(ESeq _ e1 e2)) = do
    entrynd2 <- allocNode
    vars' <- compileExprAt vars (CtxSeq1 e ctx) entrynd (Just entrynd2) e1
    _ <- compileExprAt vars' (CtxSeq2 e ctx) entrynd2 exitnd e2
    return vars

compileExprAt vars ctx entrynd Nothing (E e@(EPar _ e1 e2)) = do
    (entrynd1, _) <- compileExpr vars (CtxPar1 e ctx) Nothing e1
    (entrynd2, _) <- compileExpr vars (CtxPar2 e ctx) Nothing e2
    updateNode entrynd (I.Par [I.BB [] $ I.Goto entrynd1, I.BB [] $ I.Goto entrynd2]) [entrynd1, entrynd2]
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(EITE _ c t me)) = do
    c' <- mkScalarExpr vars c
    (entryndt, _) <- compileExpr vars (CtxITEThen e ctx) exitnd t
    case me of
         Just el -> do 
                (entrynde, _) <- compileExpr vars (CtxITEElse e ctx) exitnd
                updateNode entrynd (I.Cond [(c', I.BB [] $ I.Goto entryndt), (I.EBool True, I.BB [] $ I.Goto entrynde)]) [entryndt, entrynde]
         Nothing -> updateNode entrynd (I.Cond [(c', I.BB [] $ I.Goto entryndt), (I.EBool True, I.BB [] I.Drop)]) [entryndt]
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(EDrop _)) = do
    updateNode entrynd (I.Par [I.BB [] I.Drop]) []
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(ESet _ e1 e2)) = do
    let e1' = mkExpr vars e1
        e2' = mkExpr vars e2
    let asns = map (uncurry I.ASet) $ zip e1' e2'
    updateNode entrynd (I.Par [BB asns $ maybe I.Drop I.Goto exitnd]) $ maybeToList exitnd
    return vars

compileExprAt vars ctx entrynd Nothing (E e@(ESend _ (E (ELocation _ _ x)))) = do
    port <- mkScalarExpr vars $ eField "portnum"
    updateNode entrynd (I.Par [BB [] $ I.Send port]) []
    return vars

compileExprAt vars ctx entrynd Nothing (E e@(EFork _ v t c b)) = do
    let rel = getRelation ?r t
        cols = relCols rel
    (vars', asns) <- declAsnVar vars v (relRecordType rel) entrynd cols
    c' <- mkScalarExpr vars' c
    (entryndb, _) <- compileExpr vars' (CtxForkBody e ctx) Nothing b
    updateNode entrynd (I.Fork t c' $ I.BB asns $ I.Goto entryndb)
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(EWith _ v t c b md)) = do
    let rel = getRelation ?r t
        cols = relCols rel
    (vars', asns) <- declAsnVar vars v (relRecordType rel) entrynd cols
    c' <- mkScalarExpr vars' c
    (entryndb, _) <- compileExpr vars' (CtxWithBody e ctx) exitnd b
    case md of
         Just d -> do
             (entryndd, _) <- compileExpr vars (CtxWithDef e ctx) exitnd d
             updateNode entrynd (I.Lookup t c' (I.BB asns $ I.Goto entryndb) (I.BB asns $ I.Goto entryndd)) [entryndb, entryndd]
         Nothing -> updateNode entrynd (I.Lookup t c' (I.BB asns $ I.Goto entryndb) (I.BB [] I.Drop)) [entryndb]
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(ETyped _ (E (EVarDecl _ v)) t)) = do
    (vars', _) <- declVar vars v t entrynd
    updateNode entrynd (I.Par [I.BB [] $ maybe I.Drop I.Goto exitnd]) $ maybeToList exitnd
    return vars'

compileExprAt vars ctx entrynd exitnd (E e@(EPut _ t v)) = do
    let v' = mkExpr vars v
    updateNode entrynd (I.Par [I.BB [I.APut t v'] $ maybe I.Drop I.Goto exitnd]) $ maybeToList exitnd
    return vars

compileExprAt vars ctx entrynd exitnd (E e@(EDelete _ t c)) = do
    let c' = mkScalarExpr vars c
    updateNode entrynd (I.Par [I.BB [I.ADelete t c'] $ maybe I.Drop I.Goto exitnd]) $ maybeToList exitnd
    return vars
 
compileExprAt vars ctx entrynd exitnd (E e@(EMatch _ m cs)) = do
    cs' <- mapIdxM (\(c, a) i -> do let c' = mkMatchCond vars m c
                                    entrya_ <- allocNode
                                    (vars', asns) <- foldM (\(_vars, _asns) (v, vexp) -> do 
                                                                (vars', asns') <- declAsnVar _vars v (exprType ?r (CtxMatchExpr e ctx) $ mkExpr vars vexp) entrya_
                                                                return (vars', _asns ++ asns'))
                                                           (vars, []) $ matchVars m c
                                    (entrya, _) <- compileExpr vars' (CtxMatchVal e ctx i) exitnd a
                                    updateNode entrya_ (I.Par [I.BB asns $ I.Goto entrya]) [entrya]
                                    retrurn (c', entrya_))
            cs 
    updateNode entrynd (I.Cond $ map (\(c,entry) -> (c, I.BB [] $ I.Goto entry)) cs') $ map snd entries
    return vars

declVar :: M.Map String String -> String -> Type -> I.NodeId -> CompileState (M.Map String String, [(I.VarName, I.Type)])
declVar vars vname vtype nd = do
    let vs = var2Scalars v t
    mapM_ (\(n, t) -> addVar n t nd) vs
    return (M.insert vname (vnameAt vname nd) vars, vs)

declAsnVar :: M.Map String String -> String -> Type -> I.NodeId -> [I.Expr] -> CompileState (M.Map String String, [I.Action])
declAsnVar vars vname vtype nd vals = do
    (vars', vs) <- declVar vars vname vtype nd
    let asns = map (uncurry I.ASet) $ zip (map (I.EVar . fst) vs) vals
    return (vars', asns)



matchVars exp pat -> (String, Expr)
mkMatchCond vars m c -> I.Expr

-- function calls
-- version of expr2Statement that inlines function calls

mkScalarExpr :: (?r::Refine) => M.Map String String -> ECtx -> Expr -> [I.Expr]
mkScalarExpr vars ctx e = e where [e] = mkExpr vars ctx e

relCols :: (?r::Refine) => Relation -> [I.Expr]
relCols rel = exprTreeFlatten $ fields "" (relRecordType rel) $ \_ n -> I.ECol n

var2Scalars :: String -> Type -> [(I.VarName, I.Type)]
var2Scalars v t = exprTreeFlatten $ fields "" t $ \t n -> (v .+ n, t)

mkExpr :: (?r::Refine) => M.Map String String -> ECtx -> Expr -> [I.Expr]
mkExpr vars ctx e = exprTreeFlatten $ exprFoldCtx (mkExpr' vars) ctx e

mkExpr' :: (?r::Refine) => ECtx -> ExprNode ExprTree -> ExprTree
mkExpr' ctx (EVar _ v)                          = fields "" (varType $ getVar ?r ctx v) (\_ n -> I.EVar $ (v .+ n))
mkExpr' _   (EPacket _)                         = fields "" (tdefType $ getType ?r packetTypeName) (\_ n -> I.EPktField n)
mkExpr' _   (EField _ (Left fs) f)              = fromJust $ lookup f fs
mkExpr' _   (EBool _ b)                         = Right $ I.Bool b
mkExpr' _   (EBit _ w v)                        = Right $ I.Bit w v
mkExpr' ctx (EStruct _ c fs)                    = Left $ tag ++ fls
    where Struct _ cs = tdefType $ consType ?r c
          Constructor{..} = getConstructor ?r c
          tag = if' (needsTag cs) [("_tag", Right $ I.Bit (tagWidth cs) (tagVal cs c))] []
          fls = map (\f -> let tree = case findIndex (== f) consArgs of
                                           Just i  -> fs !! i
                                           Nothing -> defaultETree $ typ f
                                      in (name f, tree)) $ structFields cs
mkExpr' _   (ETuple _ fs)                       = Left $ mapIdx (\f i -> (show i, f)) fs 
mkExpr' _   (ESlice _ (Right e) h l)            = Right $ I.ESlice e h l
mkExpr' _   (EBinOp _ op (Right e1) (Right e2)) = Right $ I.EBinOp op e1 e2
mkExpr' _   (EUnOp _ op (Right e))              = Right $ I.EUnOp op e
mkExpr' _   (ETyped _ e _)                      = e

(.+) :: String -> String -> String
(.+) "" s  = s
(.+) s ""  = s
(.+) s1 s2 = s1 ++ "." ++ s2

type ExprTree a = Either [(String, FieldTree)] a

fields :: (?r::Refine) => String -> Type -> (I.Type -> String -> a) -> ExprTree a
fields pref t f = 
    case typ' ?r t of
         TBool _      -> Right $ f I.TBool pref
         TBit _ w     -> Right $ f (I.TInt w) pref
         TStruct _ cs -> Left $ (if' (needsTag cs) [("_tag", fields (pref .+ "_tag") (tagType cs) f)] []) ++ (map (\fl -> (name fl, fields (pref .+ name fl) (typ fl) f)) $ structFields cs)
         TTuple _ as  -> Left $ mapIdx (\t' i -> (show i, fields (pref .+ show i) t' f)) as


exprTreeFlatten :: ExprTree -> [I.Expr]
exprTreeFlatten (Right x) = [x]
exprTreeFlatten (Left ts) = concatMap (exprTreeFlatten . snd) ts

defaultETree :: (?r::Refine) => Type -> ExprTree
defaultETree t =
    case typ' ?r t of
         TBool _      -> Right $ I.EBool False
         TBit _ w     -> Right $ I.EBit w 0
         TStruct _ cs -> Left $ (if' (needsTag cs) [("_tag", defaultETree $ tagType cs)] []) ++ (map (\fl -> (name fl, defaultETree (typ fl))) $ structFields cs)
         TTuple _ as  -> Left $ mapIdx (\t' i -> (show i, defaultETree t')) as

needsTag :: [Constructor] -> Bool
needsTag cs = length cs > 1

tagWidth :: [Constructor] -> Int
tagWidth cs = bitWidth $ length cs - 1

tagType :: [Constructor] -> Type
tagType cs = TBit nopos $ tagWidth cs

tagVal :: [Constructor] -> String -> Integer
tagVal cs c = fromJust $ findIndex ((== c) . name) cs

EApply use expr2Statement first

-----
