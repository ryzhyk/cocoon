{-
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}
{-# LANGUAGE ImplicitParams, RecordWildCards #-}

-- Interface to SMT2 format

module SMT.SMTLib2(SMT2Config,
                   z3Config,
                   newSMTLib2Solver) where

import qualified Text.Parsec as P
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import System.Exit
import Control.Monad.Except
import Data.String.Utils

import Util
import PP
import SMT.SMTSolver
import SMT.SMTLib2Parse
import Ops

data SMT2Config = SMT2Config {
    s2Solver :: String,  -- Name of the solver executable
    s2Opts   :: [String] -- Arguments passed on every invocation of the solver
}

z3Config = SMT2Config {s2Solver = "z3", s2Opts = ["-smt2", "-in"]}

newSMTLib2Solver :: SMT2Config -> SMTSolver
newSMTLib2Solver config = SMTSolver { smtGetModel       = getModel config
                                    , smtCheckSAT       = checkSat config
                                    , smtGetCore        = getUnsatCore config
                                    , smtGetModelOrCore = getModelOrCore config
                                    }

------------------------------------------------------
-- Printing formulas in SMTLib2 format
------------------------------------------------------

-- convert string into a valid smtlib identifier by
-- bracketing it with '|' if necessary
mkIdent :: String -> String
mkIdent str = if valid then str else "|" ++ (replace  "|" "_" str) ++ "|"
    where valid = all (\c -> elem c ("_"++['a'..'z']++['A'..'Z']++['0'..'9'])) str
                  && notElem (head str) ['0'..'9']

class SMTPP a where
    smtpp :: (?q::SMTQuery) => a -> Doc

printQuery :: SMTQuery -> Doc
printQuery q@SMTQuery{..} = 
        let ?q = q in
        (vcat $ map smtpp smtStructs)
        $+$
        (vcat $ map smtpp smtVars)
        $+$
        (vcat $ map smtpp smtFuncs)
        $+$
        (vcat $ mapIdx (\e i -> parens $ text "assert" 
                                         <+> (parens $ char '!' <+> smtppExpr Nothing e <+> text ":named" <+> text assertName <> int i)) smtExprs)

instance SMTPP Var where
    smtpp (Var n t) = parens $  pp "declare-const"
                            <+> pp (mkIdent n)
                            <+> smtpp t

instance SMTPP Type where
    smtpp TBool       = pp "Bool"
    smtpp (TUInt w)   = pp $ "(_ BitVec " ++ show w ++ ")"
    smtpp (TStruct n) = pp n

instance SMTPP Struct where
    smtpp (Struct n fs) = parens $ pp "declare-datatypes ()" 
                                 <+> (parens $ parens $ pp n 
                                      <+> parens (pp ("mk-" ++ n) <+> (hsep $ map (\(f,t) -> parens $ pp (n ++ f) <+> smtpp t) fs)))

smtppExpr :: (?q::SMTQuery) => Maybe Function -> Expr -> Doc
smtppExpr _  (EVar n)           = pp n
smtppExpr mf (EField e f)       = parens $ text (s ++ f) <+> smtppExpr mf e
                                  where TStruct s = typ ?q mf e
smtppExpr _  (EBool True)       = pp "true"
smtppExpr _  (EBool False)      = pp "false"
smtppExpr _  (EInt w v)         = pp $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
smtppExpr mf (EStruct n fs)     = parens (pp ("mk-" ++ n) <+> (hsep $ map (smtppExpr mf) fs))
smtppExpr mf (EBinOp Neq e1 e2) = smtppExpr mf $ EUnOp Not $ EBinOp Eq e1 e2
smtppExpr mf (EBinOp op e1 e2)  = parens $ smtpp op <+> smtppExpr mf e1 <+> smtppExpr mf e2
smtppExpr mf (EUnOp op e)       = parens $ smtpp op <+> smtppExpr mf e
smtppExpr mf (ESlice e h l)     = parens $ (parens $ char '_' <+> text "extract" <+> int h <+> int l) <+> smtppExpr mf e
smtppExpr mf (ECond cs d)       = foldr (\(c,v) e -> parens $ pp "ite" <+> smtppExpr mf c <+> smtppExpr mf v <+> e) (smtppExpr mf d) cs
smtppExpr _  (EApply f [])      = ppFName f
smtppExpr mf (EApply f as)      = parens $ ppFName f <+> (hsep $ map (smtppExpr mf) as)

instance SMTPP BOp where
    smtpp Eq     = pp "="
    smtpp Neq    = error "SMTLib2.smtpp !="
    smtpp Lt     = pp "bvult"
    smtpp Gt     = pp "bvugt"
    smtpp Lte    = pp "bvule"
    smtpp Gte    = pp "bvuge"
    smtpp And    = pp "and"
    smtpp Or     = pp "or"
    smtpp Impl   = pp "=>"
    smtpp Plus   = pp "bvadd"
    smtpp Minus  = pp "bvsub"
    smtpp ShiftR = pp "bvlshr"
    smtpp ShiftL = pp "bvshl"
    smtpp Mod    = pp "bvurem"
    smtpp Concat = pp "concat"

instance SMTPP UOp where
    smtpp Not   = pp "not"

instance SMTPP Function where
    smtpp f@Function{..} = parens $   pp "define-fun" <+> ppFName funcName 
                                  <+> (parens $ hsep $ map (\(a,t) -> parens $ pp a <+> smtpp t) funcArgs) 
                                  <+> smtpp funcType
                                  <+> smtppExpr (Just f) funcDef

ppFName :: String -> Doc
ppFName f = pp $ "__fun_" ++ f

--------------------------------------------------------
---- Running solver in different modes
--------------------------------------------------------

runSolver :: SMT2Config -> Doc -> P.Parsec String () a -> a
runSolver cfg query parser = 
    let (ecode, out, er) = unsafePerformIO $ readProcessWithExitCode (s2Solver cfg) (s2Opts cfg) (show query)
    in if' (ecode == ExitSuccess || ecode == ExitFailure 1)
           (case P.parse parser "" out of
                 Left e  -> error $ "Error parsing SMT solver output: " ++ 
                                    "\nsolver input: " ++ render query ++
                                    "\nsolver stdout: " ++ out ++
                                    "\nsolver stderr: " ++ er ++
                                    "\nparser error: "++ show e
                 Right x -> x
                            {-trace "solver input: " 
                            $ trace (render quert)
                            $ trace " solver output: " 
                            $ trace out x-}) 
           (error $ "Error code returned by SMT solver: " ++ show ecode ++
                    "\nsolver input: " ++ render query ++
                    "\nsolver stdout: " ++ out ++
                    "\nsolver stderr: " ++ er)

checkSat :: SMT2Config -> SMTQuery -> Maybe Bool
checkSat cfg q = runSolver cfg query satresParser
    where query = printQuery q $$ text "(check-sat)"


getUnsatCore :: SMT2Config -> SMTQuery -> Maybe (Maybe [Int])
getUnsatCore cfg q = 
    runSolver cfg query
    $ do res <- satresParser
         case res of
              Just False -> liftM (Just . Just) unsatcoreParser
              Just True  -> return (Just Nothing)
              _          -> return Nothing
    where query = text "(set-option :produce-unsat-cores true)"
               $$ printQuery q
               $$ text "(check-sat)"
               $$ text "(get-unsat-core)"

getModel :: SMT2Config -> SMTQuery -> Maybe (Maybe Assignment)
getModel cfg q =
    runSolver cfg query
    $ do res <- satresParser
         case res of 
              Just True  -> let ?q = q in liftM (Just . Just) modelParser
              Just False -> return $ Just Nothing
              _          -> return Nothing
    where query = text "(set-option :produce-models true)"
               $$ (printQuery q)
               $$ text "(check-sat)"
               $$ text "(get-model)"

getModelOrCore :: SMT2Config -> SMTQuery -> Maybe (Either [Int] Assignment)
getModelOrCore cfg q =
    runSolver cfg query
    $ do res <- satresParser
         case res of 
              Just True  -> let ?q = q in liftM (Just . Right) modelParser
              Just False -> liftM (Just . Left)  $ errorParser *> unsatcoreParser
              _          -> return Nothing
    where query = text "(set-option :produce-unsat-cores true)"
               $$ text "(set-option :produce-models true)"
               $$ (printQuery q)
               $$ text "(check-sat)"
               $$ text "(get-model)"
               $$ text "(get-unsat-core)"
