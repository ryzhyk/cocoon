{-# LANGUAGE ImplicitParams #-}

module Expr (exprFuncs, exprRefersToPkt) where

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

-- True if e does not refer to any packet fields 
-- (it may contain function calls and references to other variables)
exprRefersToPkt :: Expr -> Bool
exprRefersToPkt (EVar _ _)         = False
exprRefersToPkt (EPacket _)        = True
exprRefersToPkt (EApply _ _ as)    = or $ map exprRefersToPkt as
exprRefersToPkt (EField _ s _)     = exprRefersToPkt s
exprRefersToPkt (ELocation _ _ as) = or $ map exprRefersToPkt as
exprRefersToPkt (EBool _ _)        = False
exprRefersToPkt (EInt _ _ _)       = False
exprRefersToPkt (EStruct _ _ fs)   = or $ map exprRefersToPkt fs
exprRefersToPkt (EBinOp _ _ l r)   = exprRefersToPkt l || exprRefersToPkt r
exprRefersToPkt (EUnOp _ _ e)      = exprRefersToPkt e
exprRefersToPkt (ECond _ cs d)     = (or $ map (\(c,e) -> exprRefersToPkt c || exprRefersToPkt e) cs) || exprRefersToPkt d
