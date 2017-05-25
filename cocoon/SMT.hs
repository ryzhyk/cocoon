{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module SMT ( struct2SMT
           , func2SMT
           , typ2SMT
           , expr2SMT
           , exprFromSMT) where

--import qualified Data.Map as M
import Data.Maybe
--import Data.List

import qualified SMT.SMTSolver as SMT
--import qualified SMT.SMTLib2   as SMT
import Syntax
import Name
import Expr
import Pos
--import NS
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

expr2SMT :: (?r::Refine) => ECtx -> Expr -> SMT.Expr
expr2SMT ctx e = snd $ exprFoldCtx expr2SMT'' ctx e

expr2SMT'' :: (?r::Refine) => ECtx -> ExprNode (Type, SMT.Expr) -> (Type, SMT.Expr)
expr2SMT'' ctx e = (fromJust $ exprNodeType ?r ctx $ exprMap (Just . fst) e, e')
    where e' = expr2SMT' e

expr2SMT' :: (?r::Refine) => ExprNode (Type, SMT.Expr) -> SMT.Expr
expr2SMT' (EVar _ v) | -- inside match case - add to dictionary
expr2SMT' (EVar _ v) | -- inside match action - replace from dictionary if in dictionary
expr2SMT' (EVar _ v) | otherwise             = SMT.EVar v
expr2SMT' (EPacket _)                       = SMT.EVar pktVar
expr2SMT' (EApply _ f as)                   = SMT.EApply f $ map snd as
expr2SMT' (EField _ (t,s) f)                = let TStruct _ cs = typ' ?r t
                                                  cs' = structFieldConstructors cs f
                                                  es = map (\c -> (SMT.EIsInstance (name c) s, SMT.EField (name c) s f)) cs'
                                              in SMT.ECond (init es) $ snd $ last es
expr2SMT' (EBool _ b)                       = SMT.EBool b
expr2SMT' (EInt _ i)                        = SMT.EInt i
expr2SMT' (EString _ s)                     = SMT.EString s
expr2SMT' (EBit _ w i)                      = SMT.EBit w i

expr2SMT' (EStruct _ c fs) | -- inside match case - convert to is- check, conjoin with fields
expr2SMT' (EStruct _ c fs) | otherwise      = SMT.EStruct c $ map snd fs
expr2SMT' (EBinOp _ op (_,e1) (_, e2))      = SMT.EBinOp op e1 e2
expr2SMT' (EUnOp _ op (_, e1))              = SMT.EUnOp op e1
expr2SMT' (EITE _ (_,i) (_,t) (Just (_,e))) = SMT.ECond [(i, t)] e
expr2SMT' (ESlice _ (_, e) h l)             = SMT.ESlice e h l
expr2SMT' (ETyped _ (_, e) _)               = e -- Do we ever need type hints in SMT?
expr2SMT' (ERelPred _ rel as)               = SMT.ERelPred rel $ map snd as
expr2SMT' (EPHolder _)                      = -- inside match case - ignore
                                              -- else - raise error
expr2SMT' (EMatch _ (_, e) cs)              = -- generate Cond expression
expr2SMT' e                                 = error $ "SMT.expr2SMT' " ++ (show $ exprMap snd e)

-- Convert constant SMT expression to Expr
exprFromSMT :: SMT.Expr -> Expr
exprFromSMT (SMT.EBool b)      = E $ EBool nopos b
exprFromSMT (SMT.EBit w i)     = E $ EBit nopos w i
exprFromSMT (SMT.EStruct n fs) = E $ EStruct nopos n $ map exprFromSMT fs
exprFromSMT e                  = error $ "SMT.exprFromSMT " ++ show e


