module Eval where

import qualified Data.Map as M
import Control.Monad.State.Strict

import Syntax
import qualified Datalog.Datalog as DL

type MENode = Maybe (ExprNode MExpr)
newtype MExpr = ME MENode
type Result  = Either Expr [(Expr, Expr)]

type KMap = M.Map String MExpr
type EvalState a = StateT (KMap, MExpr, [Expr]) IO a

eget :: EvalState KMap
eput :: KMap -> EvalState ()
emodify :: (KMap -> KMap) -> EvalState ()
eyield :: Expr -> EvalState ()
evalExpr :: Refine -> ECtx -> KMap -> Maybe Expr -> DL.Session -> Expr -> IO (Result, [Expr], KMap, Maybe Expr)
