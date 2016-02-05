-- Generic interface of an SMT solver

module SMT.SMTSolver where

import qualified Data.Map as M

import Ops

data Type = TBool
          | TUInt Int
          | TStruct String

data Struct = Struct String [(String,Type)]

data Var = Var String Type

data Expr = EVar    String
          | EField  Expr String
          | EBool   Bool
          | EInt    Int Integer
          | EStruct String [Expr]
          | EBinOp  BOp Expr Expr
          | EUnOp   UOp Expr 
          | ECond   [(Expr, Expr)] Expr

type Store = M.Map String Expr

data SMTSolver = SMTSolver {
    -- Input:  list of formula
    -- Output: Nothing    - satisfiability of the formula could not be established
    --         Just Left  - unsat core of the conjunction of formula
    --         Just Right - satisfying assignment (unassigned variables are don't cares)
    smtGetModel       :: [Expr] -> Maybe (Maybe Store),
    smtCheckSAT       :: [Expr] -> Maybe Bool,
    smtGetCore        :: [Expr] -> Maybe (Maybe [Int]),
    smtGetModelOrCore :: [Expr] -> Maybe (Either [Int] Store)
}

