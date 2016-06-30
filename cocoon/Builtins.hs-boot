{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Builtins where

import Text.PrettyPrint
import Control.Monad.Except

import Syntax
import Name
import Pos
import qualified SMT.SMTSolver as SMT

data Builtin = Builtin { bfuncName        :: String
                       , bfuncValidate    :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
                       , bfuncType        :: Refine -> ECtx -> [Expr] -> Type
                       , bfuncPrintBoogie :: [Doc] -> Doc
                       , bfuncPrintP4     :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       , bfuncToSMT       :: [SMT.Expr] -> SMT.Expr
                       , bfuncEval        :: [Expr] -> Expr
                       }

instance WithName Builtin 

builtins :: [Builtin]
