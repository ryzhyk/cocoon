{-# LANGUAGE RankNTypes, FlexibleContexts #-}

-- Interface to SMT2 format

module Builtins( Builtin(..)
               , builtins) where

import Text.PrettyPrint
import Control.Monad.Except

import Syntax
import Name
import qualified SMT.SMTSolver as SMT

data Builtin = Builtin { bfuncName        :: String
                       , bfuncNArgs       :: Int
                       , bfuncValidate    :: forall me . (MonadError String me) => Refine -> ECtx -> [Expr] -> me ()
                       , bfuncType        :: Refine -> ECtx -> [Expr] -> Type
                       , bfuncPrintBoogie :: [Expr] -> Doc
                       , bfuncPrintP4     :: [Expr] -> Doc
                       , bfuncToSMT       :: Refine -> [Expr] -> SMT.Expr
                       , bfuncEval        :: [Expr] -> Expr
                       }

instance WithName Builtin where
    name = bfuncName

builtins :: [Builtin]
builtins = []
