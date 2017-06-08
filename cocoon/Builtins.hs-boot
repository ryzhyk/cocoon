{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Builtins where

import Control.Monad.Except

import Syntax
import Name
import {-# SOURCE #-} Eval

data Builtin = Builtin { bfuncName        :: String
                       , bfuncValidate    :: forall me . (MonadError String me) => Refine -> ECtx -> Expr -> me ()
                       , bfuncType        :: Refine -> ECtx -> ExprNode (Maybe Type) -> Type
                       , bfuncEval        :: Expr -> EvalState Expr
                       }

instance WithName Builtin 

builtins :: [Builtin]
