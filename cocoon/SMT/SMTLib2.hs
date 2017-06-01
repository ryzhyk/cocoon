{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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
                   SMTPP(..),
                   smtppExpr,
                   z3Config,
                   newSMTLib2Solver,
                   ppDisRelName,
                   ppRelName) where

import qualified Text.Parsec as P
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import System.Exit
import Control.Monad.Except
import Data.String.Utils

import Name
import Util
import PP
import SMT.SMTSolver
import SMT.SMTLib2Parse
import SMT.Datalog
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
    smtpp :: SMTQuery -> a -> Doc

printQuery :: SMTQuery -> Doc
printQuery q@SMTQuery{..} = 
        (vcat $ map (smtpp q) smtStructs)
        $+$
        (vcat $ map (smtpp q) smtVars)
        $+$
        (vcat $ map (smtpp q) smtFuncs)
        $+$
        (vcat $ mapIdx (\e i -> parens $ text "assert" 
                                         <+> (parens $ char '!' <+> smtppExpr q Nothing e <+> text ":named" <+> text assertName <> int i)) smtExprs)

instance SMTPP Var where
    smtpp q (Var n t) = parens $  pp "declare-const"
                              <+> pp (mkIdent n)
                              <+> smtpp q t

instance SMTPP Type where
    smtpp _ TBool        = pp "Bool"
    smtpp _ TInt         = pp "Int"
    smtpp _ TString      = pp "String"
    smtpp _ (TBit w)     = pp $ "(_ BitVec " ++ show w ++ ")"
    smtpp _ (TStruct n)  = pp n
    smtpp q (TArray t _) = parens $ pp "Array" <+> pp "Int" <+> smtpp q t

instance SMTPP Struct where
    smtpp q (Struct n cs) = parens $ pp "declare-datatypes ()" 
                                   <+> (parens $ parens $ pp n 
                                        <+> (hsep 
                                            $ map (\(cn, fs) -> parens $ pp cn <+> (hsep $ map (\(f,t) -> parens $ pp (cn ++ f) <+> smtpp q t) fs)) cs))

smtppExpr :: SMTQuery -> Maybe Function -> Expr -> Doc
smtppExpr _ _  (EVar n)           = pp n
smtppExpr q mf (EField c e f)     = parens $ text (c ++ f) <+> smtppExpr q mf e
smtppExpr _ _  (EBool True)       = pp "true"
smtppExpr _ _  (EBool False)      = pp "false"
smtppExpr _ _  (EBit w v)         = pp $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
smtppExpr _ _  (EInt v)           = pp v
smtppExpr _ _  (EString s)        = pp s
smtppExpr q mf (EIsInstance c e)  = parens $ pp "is-" <> pp c <+> smtppExpr q mf e
smtppExpr _ _  (EStruct c [])     = pp c
smtppExpr q mf (EStruct c fs)     = parens (pp c <+> (hsep $ map (smtppExpr q mf) fs))
smtppExpr q mf (EBinOp Neq e1 e2) = smtppExpr q mf $ EUnOp Not $ EBinOp Eq e1 e2
smtppExpr q mf (EBinOp op e1 e2)  = parens $ smtpp q op <+> smtppExpr q mf e1 <+> smtppExpr q mf e2
smtppExpr q mf (EUnOp op e)       = parens $ smtpp q op <+> smtppExpr q mf e
smtppExpr q mf (ESlice e h l)     = parens $ (parens $ char '_' <+> text "extract" <+> int h <+> int l) <+> smtppExpr q mf e
smtppExpr q mf (ECond cs d)       = foldr (\(c,v) e -> parens $ pp "ite" <+> smtppExpr q mf c <+> smtppExpr q mf v <+> e) (smtppExpr q mf d) cs
smtppExpr _ _  (EApply f [])      = ppFName f
smtppExpr q mf (EApply f as)      = parens $ ppFName f <+> (hsep $ map (smtppExpr q mf) as)
smtppExpr _ _  (ERelPred r [])    = ppRelName r
smtppExpr q mf (ERelPred r as)    = parens $ ppRelName r <+> (hsep $ map (smtppExpr q mf) as)

instance SMTPP BOp where
    smtpp _ Eq     = pp "="
    smtpp _ Neq    = error "SMTLib2.smtpp !="
    smtpp _ Lt     = pp "bvult"
    smtpp _ Gt     = pp "bvugt"
    smtpp _ Lte    = pp "bvule"
    smtpp _ Gte    = pp "bvuge"
    smtpp _ And    = pp "and"
    smtpp _ Or     = pp "or"
    smtpp _ Impl   = pp "=>"
    smtpp _ Plus   = pp "bvadd"
    smtpp _ Minus  = pp "bvsub"
    smtpp _ ShiftR = pp "bvlshr"
    smtpp _ ShiftL = pp "bvshl"
    smtpp _ Mod    = pp "bvurem"
    smtpp _ Concat = pp "concat"

instance SMTPP UOp where
    smtpp _ Not   = pp "not"

instance SMTPP Function where
    smtpp q f@Function{..} = parens $   pp "define-fun" <+> ppFName funcName 
                                    <+> (parens $ hsep $ map (\(a,t) -> parens $ pp a <+> smtpp q t) funcArgs) 
                                    <+> smtpp q funcType
                                    <+> smtppExpr q (Just f) funcDef

instance SMTPP Relation where
    smtpp q (Relation n as) = (parens $ pp "declare-rel" <+> ppDisRelName n <+> (parens $ smtpp q $ TBit 64)) $$
                              (parens $ pp "declare-rel" <+> ppRelName n <+> (parens $ hsep $ map (smtpp q . varType) as))

instance SMTPP GroundRule where
    smtpp q (GroundRule r as i) = parens $ pp "rule" <+> 
                                  (parens $ pp "=>" <+> (parens $ ppDisRelName r <+> smtppExpr q Nothing (EBit 64 (fromIntegral i))) 
                                                    <+> (smtppExpr q Nothing $ ERelPred r as))
instance SMTPP Rule where
    smtpp q (Rule vs h b i) = (vcat $ map (\v -> parens $ pp "declare-var" <+> (pp $ varname $ name v) <+> smtpp q (varType v)) vs) $$
                              (parens $ pp "rule" <+> 
                                        (parens $ pp "=>" <+> smtppExpr q Nothing b' <+> smtppExpr q Nothing h'))
        where ERelPred rname _ = h
              varname x = "__" ++ rname ++ "_" ++ show i ++ "_" ++ x
              subst e = exprMap subst' e
              subst' (EVar v) = EVar $ varname v
              subst' e        = e
              b' = subst b
              h' = subst h

ppFName :: String -> Doc
ppFName f = pp $ "__fun_" ++ f

ppRelName :: String -> Doc
ppRelName r = pp $ "__rel_" ++ r

ppDisRelName :: String -> Doc
ppDisRelName r = pp $ "__dis_" ++ r



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
checkSat cfg q = Just $ runSolver cfg query satresParser
    where query = printQuery q $$ text "(check-sat)"


getUnsatCore :: SMT2Config -> SMTQuery -> Maybe (Maybe [Int])
getUnsatCore cfg q = 
    runSolver cfg query
    $ do res <- satresParser
         case res of
              False -> liftM (Just . Just) unsatcoreParser
              True  -> return (Just Nothing)
    where query = text "(set-option :produce-unsat-cores true)"
               $$ printQuery q
               $$ text "(check-sat)"
               $$ text "(get-unsat-core)"

getModel :: SMT2Config -> SMTQuery -> Maybe (Maybe Assignment)
getModel cfg q =
    runSolver cfg query
    $ do res <- satresParser
         case res of 
              True  -> let ?q = q in liftM (Just . Just) modelParser
              False -> return $ Just Nothing
    where query = text "(set-option :produce-models true)"
               $$ (printQuery q)
               $$ text "(check-sat)"
               $$ text "(get-model)"

getModelOrCore :: SMT2Config -> SMTQuery -> Maybe (Either [Int] Assignment)
getModelOrCore cfg q =
    runSolver cfg query
    $ do res <- satresParser
         case res of 
              True  -> let ?q = q in liftM (Just . Right) modelParser
              False -> liftM (Just . Left)  $ errorParser *> unsatcoreParser
    where query = text "(set-option :produce-unsat-cores true)"
               $$ text "(set-option :produce-models true)"
               $$ (printQuery q)
               $$ text "(check-sat)"
               $$ text "(get-model)"
               $$ text "(get-unsat-core)"
