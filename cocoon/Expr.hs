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

module Expr ( exprIsValidFlag
            , exprFuncs
            , exprFuncsRec
            , exprRefersToPkt
            , exprScalars
            , exprDeps, exprSubst) where

import Data.List

import Syntax
import NS
import Type
import Pos
import Name

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
exprFuncs' (EBuiltin _ _ as)  = concatMap exprFuncs' as
exprFuncs' (EField _ s _)     = exprFuncs' s
exprFuncs' (ELocation _ _ as) = concatMap exprFuncs' as
exprFuncs' (EBool _ _)        = []
exprFuncs' (EInt _ _ _)       = []
exprFuncs' (EStruct _ _ fs)   = concatMap exprFuncs' fs
exprFuncs' (EBinOp _ _ l r)   = exprFuncs' l ++ exprFuncs' r
exprFuncs' (EUnOp _ _ e)      = exprFuncs' e
exprFuncs' (ESlice _ e _ _)   = exprFuncs' e
exprFuncs' (ECond _ cs d)     = concatMap (\(c,e) -> exprFuncs' c ++ exprFuncs' e) cs ++ exprFuncs' d


-- Recursively enumerate all functions invoked by the expression
exprFuncsRec :: Refine -> Expr -> [String]
exprFuncsRec r e = let ?r = r in nub $ exprFuncsRec' e

exprFuncsRec' :: (?r::Refine) => Expr -> [String]
exprFuncsRec' (EVar _ _)         = []
exprFuncsRec' (EDotVar _ _)      = []
exprFuncsRec' (EPacket _)        = []
exprFuncsRec' (EApply _ f as)    = f:(concatMap exprFuncsRec' as) ++ maybe [] exprFuncsRec' (funcDef $ getFunc ?r f)
exprFuncsRec' (EBuiltin _ _ as)  = concatMap exprFuncsRec' as
exprFuncsRec' (EField _ s _)     = exprFuncsRec' s
exprFuncsRec' (ELocation _ _ as) = concatMap exprFuncsRec' as
exprFuncsRec' (EBool _ _)        = []
exprFuncsRec' (EInt _ _ _)       = []
exprFuncsRec' (EStruct _ _ fs)   = concatMap exprFuncsRec' fs
exprFuncsRec' (EBinOp _ _ l r)   = exprFuncsRec' l ++ exprFuncsRec' r
exprFuncsRec' (EUnOp _ _ e)      = exprFuncsRec' e
exprFuncsRec' (ESlice _ e _ _)   = exprFuncsRec' e
exprFuncsRec' (ECond _ cs d)     = concatMap (\(c,e) -> exprFuncsRec' c ++ exprFuncsRec' e) cs ++ exprFuncsRec' d

-- True if e does not refer to any packet fields 
-- (it may contain function calls and references to other variables)
exprRefersToPkt :: Expr -> Bool
exprRefersToPkt (EVar _ _)         = False
exprRefersToPkt (EDotVar _ _)      = False
exprRefersToPkt (EPacket _)        = True
exprRefersToPkt (EApply _ _ as)    = or $ map exprRefersToPkt as
exprRefersToPkt (EBuiltin _ _ as)  = or $ map exprRefersToPkt as
exprRefersToPkt (EField _ s _)     = exprRefersToPkt s
exprRefersToPkt (ELocation _ _ as) = or $ map exprRefersToPkt as
exprRefersToPkt (EBool _ _)        = False
exprRefersToPkt (EInt _ _ _)       = False
exprRefersToPkt (EStruct _ _ fs)   = or $ map exprRefersToPkt fs
exprRefersToPkt (EBinOp _ _ l r)   = exprRefersToPkt l || exprRefersToPkt r
exprRefersToPkt (EUnOp _ _ e)      = exprRefersToPkt e
exprRefersToPkt (ESlice _ e _ _)   = exprRefersToPkt e
exprRefersToPkt (ECond _ cs d)     = (or $ map (\(c,e) -> exprRefersToPkt c || exprRefersToPkt e) cs) || exprRefersToPkt d

exprScalars :: Refine -> ECtx -> Expr -> [Expr]
exprScalars r c e = 
    case typ' r c e of
         TStruct _ fs -> concatMap (exprScalars r c . EField nopos e . name) fs
         _            -> [e]

-- expression must be evaluated with evalExpr before calling this function
-- to eliminate subexpressions of the form structname{v1,v2}.f1
exprDeps :: Expr -> [Expr]
exprDeps = nub . exprDeps'

exprDeps' :: Expr -> [Expr]
exprDeps' e@(EVar _ _)         = [e]
exprDeps' e@(EDotVar _ _)      = [e]
exprDeps' e@(EPacket _)        = [e]
exprDeps'   (EApply _ _ as)    = concatMap exprDeps' as
exprDeps'   (EBuiltin _ _ as)  = concatMap exprDeps' as
exprDeps' e@(EField _ _ _)     = [e]
exprDeps'   (ELocation _ _ _)  = error "Not implemented: exprDeps' ELocation"
exprDeps'   (EBool _ _)        = []
exprDeps'   (EInt _ _ _)       = []
exprDeps'   (EStruct _ _ fs)   = concatMap exprDeps' fs
exprDeps'   (EBinOp _ _ e1 e2) = exprDeps' e1 ++ exprDeps' e2
exprDeps'   (EUnOp _ _ e)      = exprDeps' e
exprDeps'   (ESlice _ e _ _)   = exprDeps' e
exprDeps'   (ECond _ cs d)     = (concatMap (\(c,v) -> exprDeps' c ++ exprDeps' v) cs) ++ exprDeps' d


exprSubst :: Expr -> Expr -> Expr -> Expr
exprSubst arg val e               | e == arg = val
exprSubst _   _   e@(EVar _ _)               = e
exprSubst _   _   e@(EDotVar _ _)            = e
exprSubst _   _   e@(EPacket _)              = e
exprSubst arg val   (EApply _ f as)          = EApply nopos f $ map (exprSubst arg val) as
exprSubst arg val   (EBuiltin _ f as)        = EBuiltin nopos f $ map (exprSubst arg val) as
exprSubst arg val   (EField _ s f)           = EField nopos (exprSubst arg val s) f
exprSubst _   _     (ELocation _ _ _)        = error "Not implemented: exprSubst ELocation"
exprSubst _   _   e@(EBool _ _)              = e
exprSubst _   _   e@(EInt _ _ _)             = e
exprSubst arg val   (EStruct _ n fs)         = EStruct nopos n $ map (exprSubst arg val) fs
exprSubst arg val   (EBinOp _ op e1 e2)      = EBinOp nopos op (exprSubst arg val e1) (exprSubst arg val e2)
exprSubst arg val   (EUnOp _ op e)           = EUnOp nopos op $ exprSubst arg val e
exprSubst arg val   (ESlice _ e h l)         = ESlice nopos (exprSubst arg val e) h l
exprSubst arg val   (ECond _ cs d)           = ECond nopos (map (\(c,e) -> (exprSubst arg val c, exprSubst arg val e)) cs) $ exprSubst arg val d

