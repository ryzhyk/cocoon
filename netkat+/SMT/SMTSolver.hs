-- Generic interface of an SMT solver

module SMT.SMTSolver where

import qualified Data.Map as M
import Data.Maybe
import Data.List

import Ops
import Name

data Type = TBool
          | TUInt Int
          | TStruct String

instance Show Type where
    show TBool       = "bool"
    show (TUInt w)   = "uint<" ++ show w ++ ">"
    show (TStruct n) = n

data Struct = Struct { structName   :: String 
                     , structFields ::[(String,Type)]
                     }

instance WithName Struct where
    name (Struct n _) = n

data Var = Var { varName :: String
               , varType :: Type}

instance WithName Var where
    name (Var n _) = n

data Expr = EVar    String
          | EField  Expr String
          | EBool   Bool
          | EInt    Int Integer
          | EStruct String [Expr]
          | EBinOp  BOp Expr Expr
          | EUnOp   UOp Expr 
          | ECond   [(Expr, Expr)] Expr

-- Assigns values to variables.
type Assignment = M.Map String Expr

typ :: SMTQuery -> Expr -> Type
typ q (EVar n)      = varType $ fromJust $ find ((==n) . name) $ smtVars q
typ q (EField e f)  = fromJust $ lookup n fs
                      where TStruct n = typ q e
                            Struct _ fs = fromJust $ find ((== n) . name) $ smtStructs q
typ _ (EBool _)         = TBool
typ _ (EInt w _)        = TUInt w
typ _ (EStruct n _)     = TStruct n
typ q (EBinOp op e1 e2) | elem op [Eq, Lt, Gt, Lte, Gte, And, Or] = TBool
                        | elem op [Plus, Minus, Mod] = typ q e1
typ _ (EUnOp Not _)     = TBool 
typ q (ECond _ d)       = typ q d

data SMTQuery = SMTQuery { smtStructs :: [Struct]
                         , smtVars    :: [Var]
                         , smtExprs   :: [Expr]
                         }

data SMTSolver = SMTSolver {
    -- Input:  list of formula
    -- Output: Nothing    - satisfiability of the formula could not be established
    --         Just Left  - unsat core of the conjunction of formula
    --         Just Right - satisfying assignment (unassigned variables are don't cares)
    smtGetModel       :: SMTQuery -> Maybe (Maybe Assignment),
    smtCheckSAT       :: SMTQuery -> Maybe Bool,
    smtGetCore        :: SMTQuery -> Maybe (Maybe [Int]),
    smtGetModelOrCore :: SMTQuery -> Maybe (Either [Int] Assignment)
}


allSolutions :: SMTSolver -> SMTQuery -> String -> [Expr]
allSolutions solver q var = 
    -- Find one solution; block it, call solveFor recursively to find more
    case smtGetModel solver q of
         Nothing           -> error "SMTSolver.allSolutions: Failed to solve SMT query"
         Just Nothing      -> []
         Just (Just model) -> let val = model M.! var 
                                  q'  = q{smtExprs = (EUnOp Not $ EBinOp Eq (EVar var) val) : (smtExprs q)} 
                              in val:(allSolutions solver q' var)
