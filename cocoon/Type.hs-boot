module Type where

import Syntax

class WithType a where
    typ  :: a -> Type

ctxExpectType :: Refine -> ECtx -> Maybe Type
exprType :: Refine -> ECtx -> Expr -> Type
exprTypes :: Refine -> ECtx -> Expr -> [Type]
typeSubtypes :: Refine -> Type -> [Type]
typeSubtypesRec :: Refine -> Type -> [Type]
