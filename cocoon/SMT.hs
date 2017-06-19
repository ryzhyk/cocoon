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
           , exprFromSMT) where

import Data.Maybe

import qualified SMT.SMTSolver as SMT
import Syntax
import Name
import Expr
import NS
import Type
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
    SMT.Struct n $ map (\c -> SMT.Constructor (name c) $ map (\f -> SMT.Var (name f) (typ2SMT $ typ f)) $ consArgs c) cs

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
expr2SMT' ctx (EInt _ i)                           = case typ' ?r $ exprType ?r ctx $ eInt i of
                                                          TBit _ w -> SMT.EBit w i
                                                          TInt _   -> SMT.EInt i
                                                          _        -> error $ "non-integer type in SMT.expr2SMT EInt"
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

