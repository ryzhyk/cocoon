{-# LANGUAGE ImplicitParams #-}

module Eval ( KMap
            , evalExpr) where

import qualified Data.Map as M
import Data.Maybe
import Data.Bits 
import Data.List

import Syntax
import Type
import Pos
import Name
import NS

-- Key map: maps keys into their values
type KMap = M.Map String Expr

-- Partially evaluate expression: 
-- Expand function definitions, substitute variable values defined in KMap
-- When all functions are defined, the result should be an expression without
-- function calls and with only pkt variables.
evalExpr  :: (?r::Refine, ?role::Role, ?kmap::KMap) => Expr -> Expr
evalExpr (EVar _ k)                    = ?kmap M.! k
evalExpr (EApply p f as)             = 
    case funcDef func of
         Nothing -> EApply p f as'
         Just e  -> let ?kmap = foldl' (\m (a,v) -> M.insert (name a) v m) M.empty $ zip (funcArgs func) as'
                    in evalExpr e
    where as' = map evalExpr as                                     
          func = getFunc ?r f
evalExpr (EField _ s f)        = 
    case evalExpr s of
         EStruct _ _ fs -> let (TStruct _ sfs) = typ' ?r (CtxRole ?role) s
                               fidx = fromJust $ findIndex ((== f) . name) sfs
                           in fs !! fidx
         s'             -> EField nopos s' f
evalExpr (ELocation _ r ks)            = ELocation nopos r $ map evalExpr ks
evalExpr (EStruct _ s fs)              = EStruct nopos s $ map evalExpr fs
evalExpr e@(EBinOp _ op lhs rhs)         = 
    let lhs' = evalExpr lhs
        rhs' = evalExpr rhs
        TUInt _ w1 = typ' ?r (CtxRole ?role) lhs'
        TUInt _ w2 = typ' ?r (CtxRole ?role) rhs'
        w = max w1 w2
    in case (lhs', rhs') of
            (EBool _ v1, EBool _ v2)   -> case op of
                                               Eq  -> EBool nopos (v1 == v2)
                                               And -> EBool nopos (v1 && v2)
                                               Or  -> EBool nopos (v1 || v2)
                                               _   -> error $ "Eval.evalExpr " ++ show e
            (EBool _ True, _)          -> case op of
                                               Eq  -> rhs'
                                               And -> rhs'
                                               Or  -> lhs'
                                               _   -> error $ "Eval.evalExpr " ++ show e
            (EBool _ False, _)         -> case op of
                                               Eq  -> EUnOp nopos Not rhs'
                                               And -> lhs'
                                               Or  -> rhs'
                                               _   -> error $ "Eval.evalExpr " ++ show e
            (_, EBool _ True)          -> case op of
                                               Eq  -> lhs'
                                               And -> lhs'
                                               Or  -> rhs'
                                               _   -> error $ "Eval.evalExpr " ++ show e
            (_, EBool _ False)          -> case op of
                                               Eq  -> EUnOp nopos Not lhs'
                                               And -> rhs'
                                               Or  -> lhs'
                                               _   -> error $ "Eval.evalExpr " ++ show e
            (EInt _ _ v1, EInt _ _ v2) -> case op of
                                               Eq    -> EBool nopos (v1 == v2)
                                               Lt    -> EBool nopos (v1 < v2)
                                               Gt    -> EBool nopos (v1 > v2)
                                               Lte   -> EBool nopos (v1 <= v2)
                                               Gte   -> EBool nopos (v1 >= v2)
                                               Plus  -> EInt  nopos w ((v1 + v2) `mod` (1 `shiftL` w))
                                               Minus -> EInt  nopos w ((v1 - v2) `mod` (1 `shiftL` w))
                                               Mod   -> EInt  nopos w1 (v1 `mod` v2)
                                               _     -> error $ "Eval.evalExpr " ++ show e
            _                          -> EBinOp nopos op lhs' rhs'
evalExpr (EUnOp _ op e)                = 
    let e' = evalExpr e
    in case e' of
           (EBool _ v) -> case op of
                               Not -> EBool nopos (not v)
           _           -> EUnOp nopos op e'
evalExpr (ECond _ cs d)                = 
    let cs1 = map (\(e1,e2) -> (evalExpr e1, evalExpr e2)) cs
        cs2 = filter ((/= EBool nopos False) . fst) cs1
        d'  = evalExpr d
    in case break ((== EBool nopos True) . fst) cs2 of 
            ([],[])       -> d'
            (cs3,[])      -> ECond nopos cs3 d'
            ([],(_,e):_)  -> e
            (cs3,(_,e):_) -> ECond nopos cs3 e
evalExpr e                             = e
