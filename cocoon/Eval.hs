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
{-# LANGUAGE ImplicitParams #-}

module Eval ( KMap
            , evalExpr
            , evalExpr') where

import qualified Data.Map as M
import Data.Maybe
import Data.Bits 
import Data.List

import Syntax
import Type
import Pos
import Name
import NS
import Util
import Builtins

-- Key map: maps keys into their values
type KMap = M.Map String Expr

-- Partially evaluate expression: 
-- Expand function definitions, substitute variable values defined in KMap
-- When all functions are defined and all variables are mapped into values, the result should be an expression without
-- function calls and with only pkt variables.
evalExpr  :: (?r::Refine, ?c::ECtx) => KMap -> Expr -> Expr
evalExpr kmap e = let ?kmap = kmap in evalExpr' e

evalExpr'  :: (?r::Refine, ?c::ECtx, ?kmap::KMap) => Expr -> Expr
evalExpr' e@(EVar _ k)                  = case M.lookup k ?kmap of
                                              Nothing -> e
                                              Just e' -> e'
evalExpr' (EApply p f as)               = 
    case funcDef func of
         Nothing -> EApply p f as'
         Just e  -> let ?kmap = foldl' (\m (a,v) -> M.insert (name a) v m) M.empty $ zip (funcArgs func) as'
                    in evalExpr' e
    where as' = map evalExpr' as                                     
          func = getFunc ?r f
evalExpr' (EBuiltin _ f as)             = (bfuncEval $ getBuiltin f) $ map evalExpr' as
evalExpr' (EField _ s f)                = 
    case evalExpr' s of
         s'@(EStruct _ _ fs) -> let (TStruct _ sfs) = typ' ?r ?c s'
                                    fidx = fromJust $ findIndex ((== f) . name) sfs
                                in fs !! fidx
         s'                  -> EField nopos s' f
evalExpr' (ELocation _ r ks)            = ELocation nopos r $ map evalExpr' ks
evalExpr' (EStruct _ s fs)              = EStruct nopos s $ map evalExpr' fs
evalExpr' e@(EBinOp _ op lhs rhs)       = 
    let lhs' = evalExpr' lhs
        rhs' = evalExpr' rhs
        TUInt _ w1 = typ' ?r ?c lhs'
        TUInt _ w2 = typ' ?r ?c rhs'
        w = max w1 w2
    in case (lhs', rhs') of
            (EBool _ v1, EBool _ v2)   -> case op of
                                               Eq  -> EBool nopos (v1 == v2)
                                               Neq -> EBool nopos (v1 /= v2)
                                               And -> EBool nopos (v1 && v2)
                                               Or  -> EBool nopos (v1 || v2)
                                               _   -> error $ "Eval.evalExpr' " ++ show e
            (EBool _ True, _)          -> case op of
                                               Eq  -> rhs'
                                               Neq -> EUnOp nopos Not rhs'
                                               And -> rhs'
                                               Or  -> lhs'
                                               _   -> error $ "Eval.evalExpr' " ++ show e
            (EBool _ False, _)         -> case op of
                                               Eq  -> EUnOp nopos Not rhs'
                                               Neq -> rhs'
                                               And -> lhs'
                                               Or  -> rhs'
                                               _   -> error $ "Eval.evalExpr' " ++ show e
            (_, EBool _ True)          -> case op of
                                               Eq  -> lhs'
                                               Neq -> EUnOp nopos Not lhs'
                                               And -> lhs'
                                               Or  -> rhs'
                                               _   -> error $ "Eval.evalExpr' " ++ show e
            (_, EBool _ False)          -> case op of
                                               Eq  -> EUnOp nopos Not lhs'
                                               Neq -> lhs'
                                               And -> rhs'
                                               Or  -> lhs'
                                               _   -> error $ "Eval.evalExpr' " ++ show e
            (EInt _ _ v1, EInt _ _ v2) -> case op of
                                               Eq     -> EBool nopos (v1 == v2)
                                               Neq    -> EBool nopos (v1 /= v2)
                                               Lt     -> EBool nopos (v1 < v2)
                                               Gt     -> EBool nopos (v1 > v2)
                                               Lte    -> EBool nopos (v1 <= v2)
                                               Gte    -> EBool nopos (v1 >= v2)
                                               Plus   -> EInt  nopos w ((v1 + v2) `mod` (1 `shiftL` w))
                                               Minus  -> EInt  nopos w ((v1 - v2) `mod` (1 `shiftL` w))
                                               ShiftR -> EInt  nopos w (v1 `shiftR` fromInteger(v2))
                                               ShiftL -> EInt  nopos w ((v1 `shiftL` fromInteger(v2)) `mod` (1 `shiftL` w))
                                               Concat -> EInt  nopos (w1+w2) ((v1 `shiftL` w2) + v2)
                                               Mod    -> EInt  nopos w1 (v1 `mod` v2)
                                               _      -> error $ "Eval.evalExpr' " ++ show e
            (EStruct _ _ fs1, EStruct _ _ fs2) -> case op of 
                                                       Eq  -> evalExpr' $ conj $ map (\(f1,f2) -> EBinOp nopos Eq f1 f2) $ zip fs1 fs2
                                                       Neq -> evalExpr' $ disj $ map (\(f1,f2) -> EBinOp nopos Neq f1 f2) $ zip fs1 fs2
                                                       _   -> error $ "Eval.evalExpr' " ++ show e
            _                          -> EBinOp nopos op lhs' rhs'
evalExpr' (EUnOp _ op e)                = 
    let e' = evalExpr' e
    in case e' of
           (EBool _ v) -> case op of
                               Not -> EBool nopos (not v)
           _           -> EUnOp nopos op e'

evalExpr' (ESlice _ e h l)              = case evalExpr' e of
                                              EInt _ _ v -> EInt nopos (h-l+1) $ bitSlice v h l
                                              e'         -> ESlice nopos e' h l
evalExpr' (ECond _ cs d)                = 
    let cs1 = map (\(e1,e2) -> (evalExpr' e1, evalExpr' e2)) cs
        cs2 = filter ((/= EBool nopos False) . fst) cs1
        d'  = evalExpr' d
    in case break ((== EBool nopos True) . fst) cs2 of 
            ([],[])       -> d'
            (cs3,[])      -> ECond nopos cs3 d'
            ([],(_,e):_)  -> e
            (cs3,(_,e):_) -> ECond nopos cs3 e
evalExpr' e                             = e

