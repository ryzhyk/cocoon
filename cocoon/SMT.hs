{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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
{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module SMT ( struct2SMT
           , func2SMT
           , typ2SMT
           , expr2SMT
           , exprFromSMT
           , rel2DL) where

--import qualified Data.Map as M
import Data.Maybe
import Data.List
import Control.Monad.State

import qualified SMT.SMTSolver as SMT
import qualified SMT.Datalog   as DL
--import qualified SMT.SMTLib2   as SMT
import Syntax
import Name
import Expr
import Pos
import NS
import Type
import Util
--import Builtins

-- Solve equation e for variable var; returns all satisfying assignments.
--solveFor :: (?r::Refine) => Role -> [Expr] -> String -> [Expr]
--solveFor role es var = map exprFromSMT $ SMT.allSolutionsVar solver (exprs2SMTQuery role es) var
--    where solver = SMT.newSMTLib2Solver SMT.z3Config

--enumSolutions :: (?r::Refine) => Role -> [Expr] -> [M.Map String Expr]
--enumSolutions role es = map (M.map exprFromSMT) models
--    where q = exprs2SMTQuery role es
--          solver = SMT.newSMTLib2Solver SMT.z3Config
--          models = SMT.allSolutions solver q

--exprs2SMTQuery :: (?r::Refine) => Role -> [Expr] -> SMT.SMTQuery
--exprs2SMTQuery role es = let ?role = role in
--                         let es' = map expr2SMT es
--                             smtvs = (SMT.Var pktVar (typ2SMT (CtxRole role) $ TUser nopos packetTypeName)) : 
--                                     (map (\k -> SMT.Var (name k) (typ2SMT (CtxRole role) k)) $ roleKeys role ++ roleLocals role ++ roleForkVars role)
--                             structs = mapMaybe (\d -> case tdefType d of
--                                                            TStruct _ cs -> Just $ struct2SMT (tdefName d) cs
--                                                            _            -> Nothing) 
--                                                $ refineTypes ?r
--                             smtfuncs = map (func2SMT . getFunc ?r) $ sortBy compareFuncs $ nub $ concatMap (exprFuncsRec ?r) es
--                         in SMT.SMTQuery structs smtvs smtfuncs es'

--compareFuncs :: (?r::Refine) => String -> String -> Ordering
--compareFuncs n1 n2 = if elem n1 f2dep 
--                        then LT
--                        else if elem n2 f1dep
--                                then GT
--                                else compare n1 n2
--    where f1 = getFunc ?r n1
--          f2 = getFunc ?r n2
--          f1dep = maybe [] (exprFuncsRec ?r) $ funcDef f1
--          f2dep = maybe [] (exprFuncsRec ?r) $ funcDef f2

struct2SMT :: (?r::Refine) => String -> [Constructor] -> SMT.Struct
struct2SMT n cs =
    SMT.Struct n $ map (\c -> (name c, map (\f -> (name f, typ2SMT $ typ f)) $ consArgs c)) cs

func2SMT :: (?r::Refine) => Function -> SMT.Function
func2SMT f@Function{..} = SMT.Function funcName 
                                       (map (\a -> (name a, typ2SMT a)) funcArgs) 
                                       (typ2SMT funcType)
                                       (expr2SMT (CtxFunc f CtxRefine)
                                                 $ maybe (error $ "SMT.func2SMT: undefined function " ++ name f)
                                                         id
                                                         funcDef)

typ2SMT :: (?r::Refine, WithType a) => a -> SMT.Type
typ2SMT x = case typ' ?r x of
                 TBool _      -> SMT.TBool
                 TInt _       -> SMT.TInt
                 TString _    -> SMT.TString
                 TBit _ w     -> SMT.TBit w
                 t@TStruct{}  -> SMT.TStruct $ name $ structTypeDef ?r t
                 TArray _ t l -> SMT.TArray (typ2SMT t) l
                 TLocation _  -> SMT.TBit 32 -- TODO: properly encode location to SMT as ADT with multiple constructors
                 t            -> error $ "SMT.typ2SMT " ++ show t

-- TODO: preprocess expression, substituting variables in the action
-- clauses of match expressions

expr2SMT :: (?r::Refine) => ECtx -> Expr -> SMT.Expr
expr2SMT ctx e = snd $ exprFoldCtx expr2SMT'' ctx e

expr2SMT'' :: (?r::Refine) => ECtx -> ExprNode (Type, SMT.Expr) -> (Type, SMT.Expr)
expr2SMT'' ctx e = (fromJust $ exprNodeType ?r ctx $ exprMap (Just . fst) e, e')
    where e' = expr2SMT' ctx e

expr2SMT' :: (?r::Refine) => ECtx -> ExprNode (Type, SMT.Expr) -> SMT.Expr
expr2SMT' ctx (EVarDecl _ _) | ctxInMatchPat ctx   = SMT.EBool True -- inside match case - no constraint on the field
expr2SMT' _   (EVar _ v)                           = SMT.EVar v
expr2SMT' _   (EPacket _)                          = SMT.EVar pktVar
expr2SMT' _   (EApply _ f as)                      = SMT.EApply f $ map snd as
expr2SMT' _   (EBuiltin _ _ _)                     = error $ "not implemented:  SMT.expr2SMT EBuiltin"
expr2SMT' _   (EField _ (t,s) f)                   = let TStruct _ cs = typ' ?r t
                                                         cs' = structFieldConstructors cs f
                                                         es = map (\c -> (SMT.EIsInstance (name c) s, SMT.EField (name c) s f)) cs'
                                                     in SMT.ECond (init es) $ snd $ last es
expr2SMT' _   (EBool _ b)                          = SMT.EBool b
expr2SMT' _   (EInt _ i)                           = SMT.EInt i
expr2SMT' _   (EString _ s)                        = SMT.EString s
expr2SMT' _   (EBit _ w i)                         = SMT.EBit w i
expr2SMT' ctx (EStruct _ c fs) | ctxInMatchPat ctx = let -- inside match case - convert to is- check, conjoin with fields
                                                         ctx'@(CtxMatchPat (EMatch _ e _) _ _) = fromJust $ ctxInMatchPat' ctx
                                                         e' = expr2SMT ctx' e
                                                         c' = SMT.EIsInstance c $ ctx2Field e' ctx
                                                     in SMT.conj $ c' : (map snd fs)
                               | otherwise         = SMT.EStruct c $ map snd fs
expr2SMT' _   (EBinOp _ op (_,e1) (_, e2))         = SMT.EBinOp op e1 e2
expr2SMT' _   (EUnOp _ op (_, e1))                 = SMT.EUnOp op e1
expr2SMT' _   (EITE _ (_,i) (_,t) (Just (_,e)))    = SMT.ECond [(i, t)] e
expr2SMT' _   (ESlice _ (_, e) h l)                = SMT.ESlice e h l
expr2SMT' _   (ETyped _ (_, e) _)                  = e -- Do we ever need type hints in SMT?
expr2SMT' _   (ERelPred _ rel as)                  = SMT.ERelPred rel $ map snd as
expr2SMT' ctx (EPHolder _) | ctxInMatchPat ctx     = SMT.EBool True -- inside match case - no constraint on the field
expr2SMT' _   (EMatch _ _ cs)                      = SMT.ECond (map (\(c,e) -> (snd c, snd e)) $ init cs) (snd $ snd $ last cs)
expr2SMT' _   e                                    = error $ "SMT.expr2SMT' " ++ (show $ exprMap snd e)

--- r, m, Cons1{_,_,Cons2{x,_}} ===> m.f1.f2
ctx2Field :: (?r::Refine) => SMT.Expr -> ECtx -> SMT.Expr
ctx2Field pref CtxMatchPat{}                         = pref
ctx2Field pref (CtxTyped _ pctx)                     = ctx2Field pref pctx
ctx2Field pref (CtxStruct (EStruct _ c _) pctx i)    = let cons = getConstructor ?r c in
                                                       SMT.EField c (ctx2Field pref pctx) (name $ consArgs cons !! i)
ctx2Field pref ctx                                   = error $ "SMT.ctx2Field " ++ show pref ++ " " ++ show ctx


-- Convert constant SMT expression to Expr
exprFromSMT :: SMT.Expr -> Expr
exprFromSMT (SMT.EBool b)      = eBool b
exprFromSMT (SMT.EBit w i)     = eBit w i
exprFromSMT (SMT.EInt i)       = eInt i
exprFromSMT (SMT.EStruct n fs) = eStruct n $ map exprFromSMT fs
exprFromSMT e                  = error $ "SMT.exprFromSMT " ++ show e


rel2DL :: (?r::Refine) => Relation -> ((DL.Relation, [DL.Rule]), [ [(DL.Relation, [DL.Rule])] ])
rel2DL rel = ((rel', rules), constrs)
    where rel' = DL.Relation (name rel) $ map (\arg -> SMT.Var (name arg) (typ2SMT arg)) $ relArgs rel
          rules = maybe []
                        (mapIdx (\rl@Rule{..} i -> let replacePH :: ECtx -> ENode -> State Int Expr
                                                       replacePH ctx (EPHolder _) | ctxInRuleL ctx || ctxInRelPred ctx = do
                                                           idx <- get
                                                           modify (+1)
                                                           return $ eVar $ "__ph" ++ show idx
                                                       replacePH _   e = return $ E e
                                                       (ruleLHS', ruleRHS') = evalState (do lhs <- mapIdxM (\l i' -> exprFoldCtxM replacePH (CtxRuleL rel rl i') l) ruleLHS
                                                                                            rhs <- mapM (exprFoldCtxM replacePH (CtxRuleR rel rl)) ruleRHS
                                                                                            return (lhs, rhs)) 0
                                                       rl' = Rule nopos ruleLHS' ruleRHS'
                                                       h = SMT.ERelPred (name rel) $ mapIdx (\e i' -> expr2SMT (CtxRuleL rel rl' i') e) ruleLHS'
                                                       hvars = concat $ mapIdx (\e i' -> exprVars (CtxRuleL rel rl' i') e) ruleLHS'
                                                       b = SMT.conj $ map (expr2SMT (CtxRuleR rel rl')) ruleRHS'
                                                       bvars = concatMap (exprVars (CtxRuleR rel rl')) ruleRHS'
                                                       vars = nub
                                                              $ map (\(vname, ctx) -> SMT.Var vname $ typ2SMT $ exprType ?r ctx $ eVar vname)
                                                              $ hvars ++ bvars
                                                   in DL.Rule vars h b $ fromIntegral i))
                        $ relDef rel
          constrs = mapIdx (constr2DL rel) $ relConstraints rel

constr2DL :: (?r::Refine) => Relation -> Constraint -> Int -> [(DL.Relation, [DL.Rule])]
constr2DL rel (PrimaryKey _ fs) _            = pkeyIndex rel fs ++ uniqueConstr rel fs
constr2DL rel (Unique _ fs)     _            = uniqueConstr rel fs
constr2DL rel (Check _ e)       i            = [fst $ rel2DL rel']
    where relname = name rel ++ "_check_" ++ show i
          as = relArgs rel
          rel' = Relation nopos False relname as [] Nothing 
                          $ Just [Rule nopos (map (eVar . name) as) 
                                       [eRelPred (name rel) (map (eVar . name) as), eNot e]]
constr2DL rel (ForeignKey _ fs rrel _) i     = [fst $ rel2DL rel']
    where -- R_foreign_i <- RRel(x,_), not RR_primary()
          relname = name rel ++ "_foreign_" ++ show i
          as = relArgs rel
          rel' = Relation nopos False relname as [] Nothing
                          $ Just [Rule nopos (map (eVar . name) as) 
                                       [ eRelPred (name rel) (map (eVar . name) as)
                                       , eNot $ eRelPred (primaryIdxName rrel) fs ]]

primaryIdxName :: String -> String
primaryIdxName rel = rel ++ "_primary_"

pkeyIndex :: (?r::Refine) => Relation -> [Expr] -> [(DL.Relation, [DL.Rule])]
pkeyIndex rel fs = [fst $ rel2DL rel']
    where -- R_primary(x) <- R(x,y)
          relname = primaryIdxName $ name rel
          as = relArgs rel
          keys = mapIdx (\f i -> Field nopos ("col" ++ show i) $ exprType ?r (CtxRelKey rel) f) fs
          rel' = Relation nopos False relname keys [] Nothing
                          $ Just [Rule nopos fs [eRelPred (name rel) (map (eVar . name) as)]]


uniqueConstr :: (?r::Refine) => Relation -> [Expr] -> [(DL.Relation, [DL.Rule])]
uniqueConstr rel fs = [fst $ rel2DL rel']
    where -- R_unique_(x1,x2) <- R(x1), R(x2), x1!=x2, x1.f == x2.f
          as1 = map (\f -> f{fieldName = fieldName f ++ "1"}) $ relArgs rel
          as2 = map (\f -> f{fieldName = fieldName f ++ "2"}) $ relArgs rel
          relname = name rel ++ "_unique_" ++ (intercalate "_" $ map show fs)
          neq = disj $ map (\(f1, f2) -> eNot $ eBinOp Eq (eVar $ name f1) (eVar $ name f2)) $ zip as1 as2 
          rename suff = exprVarRename (++suff)
          eq  = conj $ map (\f -> let fcond = fieldCond (CtxRelKey rel) f
                                      fcond1 = rename "1" fcond
                                      fcond2 = rename "2" fcond
                                  in conj [fcond1, fcond2, eBinOp Eq (rename "1" f) (rename "2" f)]) fs
          rel' = Relation nopos False relname (as1 ++ as2) [] Nothing 
                          $ Just [Rule nopos (map (eVar . name) $ as1 ++ as2) 
                                              [ eRelPred (name rel) (map (eVar . name) as1)
                                              , eRelPred (name rel) (map (eVar . name) as2)
                                              , neq, eq]]

fieldCond :: (?r::Refine) => ECtx -> Expr -> Expr
fieldCond ctx e = conj $ execState (exprTraverseCtxM (fieldCond' ?r) ctx e) []

fieldCond' :: Refine -> ECtx -> ENode -> State [Expr] ()
fieldCond' _ _   (EVar _ _)      = return ()
fieldCond' r ctx (EField _ e f)  = do 
    let TStruct _ cs = typ' r $ exprType r ctx e
    let cs' = structFieldConstructors cs f
    if length cs == length cs'
       then return ()
       else modify ((eMatch e $ map (\c -> (eStruct (name c) (map (\_ -> ePHolder) $ consArgs c), eTrue)) cs' ++ [(ePHolder, eFalse)]):)
fieldCond' _ _   e               = error $ "SMT.fieldCond' " ++ show e
