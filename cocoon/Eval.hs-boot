module Eval where

import qualified Data.Map as M
import Control.Monad.State.Strict

import Syntax
import qualified SMT.Datalog as DL

type MENode = Maybe (ExprNode MExpr)
newtype MExpr = ME MENode

type KMap = M.Map String MExpr
type EvalState a = StateT (KMap, [Expr]) IO a

eget :: EvalState KMap
eput :: KMap -> EvalState ()
emodify :: (KMap -> KMap) -> EvalState ()
eyield :: Expr -> EvalState ()
evalExpr :: Refine -> ECtx -> KMap -> DL.Session -> Expr -> IO ([Expr], KMap)
