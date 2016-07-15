{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module SMT ( solveFor
           , enumSolutions) where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import qualified SMT.SMTSolver as SMT
import qualified SMT.SMTLib2   as SMT
import Syntax
import Name
import Expr
import Pos
import NS
import Type
import Builtins

-- Solve equation e for variable var; returns all satisfying assignments.
solveFor :: (?r::Refine) => Role -> [Expr] -> String -> [Expr]
solveFor role es var = map exprFromSMT $ SMT.allSolutionsVar solver (exprs2SMTQuery role es) var
    where solver = SMT.newSMTLib2Solver SMT.z3Config

enumSolutions :: (?r::Refine) => Role -> [Expr] -> [M.Map String Expr]
enumSolutions role es = map (M.map exprFromSMT) models
    where q = exprs2SMTQuery role es
          solver = SMT.newSMTLib2Solver SMT.z3Config
          models = SMT.allSolutions solver q

exprs2SMTQuery :: (?r::Refine) => Role -> [Expr] -> SMT.SMTQuery
exprs2SMTQuery role es = let ?role = role in
                         let es' = map expr2SMT es
                             smtvs = (SMT.Var pktVar (typ2SMT (CtxRole role) $ TUser nopos packetTypeName)) : 
                                     (map (\k -> SMT.Var (name k) (typ2SMT (CtxRole role) k)) $ roleKeys role ++ roleLocals role ++ roleForkVars role)
                             structs = mapMaybe (\d -> case tdefType d of
                                                            TStruct _ fs -> Just $ SMT.Struct (tdefName d) $ map (\f -> (name f, typ2SMT (CtxRole ?role) f)) fs
                                                            _            -> Nothing) 
                                                $ refineTypes ?r
                             smtfuncs = map (func2SMT . getFunc ?r) $ sortBy compareFuncs $ nub $ concatMap (exprFuncsRec ?r) es
                         in SMT.SMTQuery structs smtvs smtfuncs es'

compareFuncs :: (?r::Refine) => String -> String -> Ordering
compareFuncs n1 n2 = if elem n1 f2dep 
                        then LT
                        else if elem n2 f1dep
                                then GT
                                else compare n1 n2
    where f1 = getFunc ?r n1
          f2 = getFunc ?r n2
          f1dep = maybe [] (exprFuncsRec ?r) $ funcDef f1
          f2dep = maybe [] (exprFuncsRec ?r) $ funcDef f2

func2SMT :: (?r::Refine) => Function -> SMT.Function
func2SMT f@Function{..} = SMT.Function funcName 
                                       (map (\a -> (name a, typ2SMT (CtxFunc f) a)) funcArgs) 
                                       (typ2SMT (CtxFunc f) funcType)
                                       (expr2SMT $ maybe (error $ "SMT.func2SMT: undefined function " ++ name f)
                                                         id
                                                         funcDef)

typ2SMT :: (?r::Refine, WithType a) => ECtx -> a -> SMT.Type
typ2SMT ctx x = case typ'' ?r ctx x of
                     TBool _      -> SMT.TBool
                     TUInt _ w    -> SMT.TUInt w
                     TUser _ n    -> SMT.TStruct n
                     TArray _ t l -> SMT.TArray (typ2SMT ctx t) l
                     TLocation _  -> SMT.TUInt 32 -- TODO: properly encode location to SMT as ADT with multiple constructors
                     t            -> error $ "SMT.typ2SMT " ++ show t

expr2SMT :: (?r::Refine) => Expr -> SMT.Expr
expr2SMT (EVar _ k)          = SMT.EVar k
expr2SMT (EPacket _)         = SMT.EVar pktVar
expr2SMT (EApply _ f as)     = SMT.EApply f $ map expr2SMT as
expr2SMT (EField _ s f)      = SMT.EField (expr2SMT s) f
expr2SMT (EBool _ b)         = SMT.EBool b
expr2SMT (EInt _ w i)        = SMT.EInt w i
expr2SMT (EStruct _ s fs)    = SMT.EStruct s $ map expr2SMT fs
expr2SMT (EBinOp _ op e1 e2) = SMT.EBinOp op (expr2SMT e1) (expr2SMT e2)
expr2SMT (EUnOp _ op e1)     = SMT.EUnOp op (expr2SMT e1)
expr2SMT (ECond _ cs d)      = SMT.ECond (map (\(c,v) -> (expr2SMT c, expr2SMT v)) cs) (expr2SMT d)
expr2SMT (ESlice _ e h l)    = SMT.ESlice (expr2SMT e) h l
expr2SMT (EBuiltin _ f as)   = (bfuncToSMT $ getBuiltin f) $ map expr2SMT as
expr2SMT e                   = error $ "SMT.expr2SMT " ++ show e

-- Convert constant SMT expression to Expr
exprFromSMT :: SMT.Expr -> Expr
exprFromSMT (SMT.EBool b)      = EBool nopos b
exprFromSMT (SMT.EInt w i)     = EInt nopos w i
exprFromSMT (SMT.EStruct n fs) = EStruct nopos n $ map exprFromSMT fs
exprFromSMT e                  = error $ "SMT.exprFromSMT " ++ show e


