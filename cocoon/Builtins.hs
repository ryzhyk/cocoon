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
import Boogie.Boogie
import Boogie.BoogieHelpers
import Util
import qualified SMT.SMTSolver as SMT

data Builtin = Builtin { bfuncName        :: String
                       , bfuncValidate    :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
                       , bfuncType        :: Refine -> ECtx -> [Expr] -> Type
                       , bfuncPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       , bfuncPrintP4     :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
                       , bfuncToSMT       :: [SMT.Expr] -> SMT.Expr
                       , bfuncEval        :: [Expr] -> Expr
                       }

instance WithName Builtin where
    name = bfuncName

builtins :: [Builtin]
builtins = [arraySelect, arrayArray]

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

arraySelectPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
arraySelectPrintBoogie _ _ _ args = arr <> (brackets idx)
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


{- array!(x1, x2, ...) -}

arrayArrayValidate :: forall me . (MonadError String me) => Refine -> ECtx -> Pos -> [Expr] -> me ()
arrayArrayValidate r ctx p args = do
    assertR r (length args > 0) p "select! requires at least one argument"
    mapM_ (\a -> matchType r ctx a (head args)) $ tail args
        
arrayArrayType :: Refine -> ECtx -> [Expr] -> Type
arrayArrayType r ctx args = TArray nopos (typ' r ctx $ head args) (length args) 

arrayArrayPrintBoogie :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
arrayArrayPrintBoogie r ctx args bgargs = 
    foldIdx (\e a i -> parens $ e <> (brackets $ pp i <+> pp ":=" <+> a)) (apply (emptyTypeFuncName r $ arrayArrayType r ctx args) []) bgargs

arrayArrayPrintP4 :: Refine -> ECtx -> [Expr] -> [Doc] -> Doc
arrayArrayPrintP4 r ctx args p4args = 
    case typ' r ctx $ head args of
         TBool _ -> parens $ hsep $ punctuate (pp " |") $ mapIdx mkBit p4args
         _       -> error "Builtins.arrayArrayPrintP4 not implemented"
    where mkBit a i = parens $ (parens $ pp "(bit<" <> pp len <> pp ">)" <> (parens $ pp "(bit<1>)" <> a)) <+> pp "<<" <+> pp i
          len = length p4args

arrayArrayToSMT :: [SMT.Expr] -> SMT.Expr
arrayArrayToSMT _ = error "Not implemented: arrayArrayToSMT"
--parens $ (parens $ pp "as const" <+> (parens $ pp "Array Int" <+> t)) <+> defval


arrayArrayEval :: [Expr] -> Expr
arrayArrayEval args = EBuiltin nopos "array" args

arrayArray = Builtin "array" 
                      arrayArrayValidate
                      arrayArrayType
                      arrayArrayPrintBoogie
                      arrayArrayPrintP4
                      arrayArrayToSMT
                      arrayArrayEval
