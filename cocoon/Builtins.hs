{-# LANGUAGE RankNTypes, FlexibleContexts #-}

-- Interface to SMT2 format

module Builtins( Builtin(..)
               , builtins) where

import Text.PrettyPrint
import Control.Monad.Except

import Syntax
import Name
import Pos
import Type
import PP
import qualified SMT.SMTSolver as SMT

data Builtin = Builtin { bfuncName        :: String
                       , bfuncValidate    :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
                       , bfuncType        :: Refine -> ECtx -> [Expr] -> Type
                       , bfuncPrintBoogie :: [Doc] -> Doc
                       , bfuncPrintP4     :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       , bfuncToSMT       :: [SMT.Expr] -> SMT.Expr
                       , bfuncEval        :: [Expr] -> Expr
                       }

instance WithName Builtin where
    name = bfuncName

builtins :: [Builtin]
builtins = [arraySelect]

{- select!(array, index) -}

arraySelectValidate :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
arraySelectValidate r ctx p args = do
    assertR r (length args == 2) p "select! requires two arguments"
    let [arr, idx] = args
    assertR r (isArray r ctx arr) (pos $ head args) "the first argument of select! must be an array"
    assertR r (isUInt r ctx idx) (pos $ head args) "the second argument of select! must be a uint"

arraySelectType :: Refine -> ECtx -> [Expr] -> Type
arraySelectType r ctx args = t
    where (a:_) = args
          TArray _ t _ = typ' r ctx a

arraySelectPrintBoogie :: [Doc] -> Doc
arraySelectPrintBoogie args = arr <> (brackets idx)
    where [arr, idx] = args

arraySelectPrintP4 :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
arraySelectPrintP4 r ctx args p4args = 
    let [arr, _]  = args
        [p4arr, p4idx] = p4args
        TArray _ t _ = typ' r ctx arr in
    case typ' r ctx t of
         TBool _ -> parens $ (parens $ (parens $ p4arr <+> pp ">>" <+> p4idx) <+> pp "&" <+> pp "0x1") <+> pp "==" <+> pp "0x1"
         _       -> error "Builtins.arraySelectPrintP4 not implemented"

arraySelectToSMT :: [SMT.Expr] -> SMT.Expr
arraySelectToSMT args = SMT.EApply "select" args

arraySelectEval :: [Expr] -> Expr
arraySelectEval args = 
    let [arr, idx] = args in
    case arr of
         EBuiltin _ "array" elems -> case idx of
                                          EInt _ _ i -> elems !! fromInteger i
                                          _          -> EBuiltin nopos "select" [arr, idx]
         _                        -> EBuiltin nopos "select" [arr, idx]

arraySelect = Builtin "select" 
                      arraySelectValidate
                      arraySelectType
                      arraySelectPrintBoogie
                      arraySelectPrintP4
                      arraySelectToSMT
                      arraySelectEval
