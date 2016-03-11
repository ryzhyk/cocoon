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
import Control.Applicative hiding (empty)
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
                                         <+> (parens $ char '!' <+> smtpp e <+> text ":named" <+> text assertName <> int i)) smtExprs)

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

instance SMTPP Expr where
    smtpp (EVar n)          = pp n
    smtpp (EField e f)      = parens $ text (s ++ f) <+> smtpp e
                              where TStruct s = typ ?q e
    smtpp (EBool True)      = pp "true"
    smtpp (EBool False)     = pp "false"
    smtpp (EInt w v)        = pp $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
    smtpp (EStruct n fs)    = parens (pp ("mk-" ++ n) <+> (hsep $ map smtpp fs))
    smtpp (EBinOp op e1 e2) = parens $ smtpp op <+> smtpp e1 <+> smtpp e2
    smtpp (EUnOp op e)      = parens $ smtpp op <+> smtpp e
    smtpp (ECond cs d)      = foldr (\(c,v) e -> parens $ pp "ite" <+> smtpp c <+> smtpp v <+> e) (smtpp d) cs
    smtpp (EApply f [])     = pp f
    smtpp (EApply f as)     = parens $ pp f <+> (hsep $ map smtpp as)

instance SMTPP BOp where
    smtpp Eq    = pp "="
    smtpp Lt    = pp "bvult"
    smtpp Gt    = pp "bvugt"
    smtpp Lte   = pp "bvule"
    smtpp Gte   = pp "bvuge"
    smtpp And   = pp "and"
    smtpp Or    = pp "or"
    smtpp Plus  = pp "bvadd"
    smtpp Minus = pp "bvsub"
    smtpp Mod   = pp "bvurem"

instance SMTPP UOp where
    smtpp Not   = pp "not"

instance SMTPP Function where
    smtpp Function{..} = parens $   pp "define-fun" <+> pp funcName 
                                <+> (parens $ hsep $ map (\(a,t) -> parens $ pp a <+> smtpp t) funcArgs) 
                                <+> smtpp funcType
                                <+> smtpp funcDef

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
