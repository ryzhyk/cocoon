module Type where

import Syntax

ctxExpectType :: Refine -> ECtx -> Maybe Type
exprType :: Refine -> ECtx -> Expr -> Type
