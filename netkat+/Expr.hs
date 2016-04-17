{-# LANGUAGE ImplicitParams #-}

module Expr ( exprIsValidFlag
            , exprFuncs
            , exprFuncsRec
            , exprRefersToPkt) where

import Data.List

import Syntax
import NS

exprIsValidFlag e = case e of 
                         EField _ _ f -> f == "valid"
                         _            -> False

-- Non-recursively enumerate all functions invoked by the expression
exprFuncs :: Refine -> Expr -> [String]
exprFuncs r e = let ?r = r in nub $ exprFuncs' e

exprFuncs' :: (?r::Refine) => Expr -> [String]
exprFuncs' (EVar _ _)         = []
exprFuncs' (EDotVar _ _)      = []
exprFuncs' (EPacket _)        = []
exprFuncs' (EApply _ f as)    = f:(concatMap exprFuncs' as)
exprFuncs' (EField _ s _)     = exprFuncs' s
exprFuncs' (ELocation _ _ as) = concatMap exprFuncs' as
exprFuncs' (EBool _ _)        = []
exprFuncs' (EInt _ _ _)       = []
exprFuncs' (EStruct _ _ fs)   = concatMap exprFuncs' fs
exprFuncs' (EBinOp _ _ l r)   = exprFuncs' l ++ exprFuncs' r
exprFuncs' (EUnOp _ _ e)      = exprFuncs' e
exprFuncs' (ECond _ cs d)     = concatMap (\(c,e) -> exprFuncs' c ++ exprFuncs' e) cs ++ exprFuncs' d


-- Recursively enumerate all functions invoked by the expression
exprFuncsRec :: Refine -> Expr -> [String]
exprFuncsRec r e = let ?r = r in nub $ exprFuncsRec' e

exprFuncsRec' :: (?r::Refine) => Expr -> [String]
exprFuncsRec' (EVar _ _)         = []
exprFuncsRec' (EDotVar _ _)      = []
exprFuncsRec' (EPacket _)        = []
exprFuncsRec' (EApply _ f as)    = f:(concatMap exprFuncsRec' as) ++ maybe [] exprFuncsRec' (funcDef $ getFunc ?r f)
exprFuncsRec' (EField _ s _)     = exprFuncsRec' s
exprFuncsRec' (ELocation _ _ as) = concatMap exprFuncsRec' as
exprFuncsRec' (EBool _ _)        = []
exprFuncsRec' (EInt _ _ _)       = []
exprFuncsRec' (EStruct _ _ fs)   = concatMap exprFuncsRec' fs
exprFuncsRec' (EBinOp _ _ l r)   = exprFuncsRec' l ++ exprFuncsRec' r
exprFuncsRec' (EUnOp _ _ e)      = exprFuncsRec' e
exprFuncsRec' (ECond _ cs d)     = concatMap (\(c,e) -> exprFuncsRec' c ++ exprFuncsRec' e) cs ++ exprFuncsRec' d

-- True if e does not refer to any packet fields 
-- (it may contain function calls and references to other variables)
exprRefersToPkt :: Expr -> Bool
exprRefersToPkt (EVar _ _)         = False
exprRefersToPkt (EDotVar _ _)      = False
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
