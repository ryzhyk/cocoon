{-# LANGUAGE ImplicitParams #-}

module Expr (exprFuncs) where

import Data.List

import Syntax
import NS

-- Recursively enumerate all functions invoked by the expression
exprFuncs :: (?r::Refine) => Expr -> [String]
exprFuncs = nub . exprFuncs'

exprFuncs' :: (?r::Refine) => Expr -> [String]
exprFuncs' (EVar _ _)         = []
exprFuncs' (EPacket _)        = []
exprFuncs' (EApply _ f as)    = f:(concatMap exprFuncs' as) ++ maybe [] exprFuncs' (funcDef $ getFunc ?r f)
exprFuncs' (EField _ s _)     = exprFuncs' s
exprFuncs' (ELocation _ _ as) = concatMap exprFuncs' as
exprFuncs' (EBool _ _)        = []
exprFuncs' (EInt _ _ _)       = []
exprFuncs' (EStruct _ _ fs)   = concatMap exprFuncs' fs
exprFuncs' (EBinOp _ _ l r)   = exprFuncs' l ++ exprFuncs' r
exprFuncs' (EUnOp _ _ e)      = exprFuncs' e
exprFuncs' (ECond _ cs d)     = concatMap (\(c,e) -> exprFuncs' c ++ exprFuncs' e) cs ++ exprFuncs' d
