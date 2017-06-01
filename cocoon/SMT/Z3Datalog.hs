{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

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

-- Z3-based Datalog engine

{-# LANGUAGE RecordWildCards, ImplicitParams #-}

module SMT.Z3Datalog(z3DatalogEngine) where

import qualified Text.Parsec as P
import Text.PrettyPrint
import System.Process
import GHC.IO.Handle
import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Map as M

import Name
import Ops
import PP
import SMT.Datalog
import SMT.SMTLib2
import SMT.SMTLib2Parse
import SMT.SMTSolver

data Z3Session = Z3Session { z3q     :: SMTQuery
                           , z3rel   :: [Relation]
                           , z3hto   :: Handle
                           , z3hfrom :: Handle
                           , z3hp    :: ProcessHandle}
z3DatalogEngine = DatalogEngine {newSession = z3NewSession}

z3NewSession :: [Struct] -> [Function] -> [Relation] -> IO Session
z3NewSession structs funcs rels = do
    (hlocal, hremote) <- createPipe
    let cproc = (proc "z3" ["-smt2", "-in"]){ std_out = UseHandle hremote
                                            , std_in  = CreatePipe
                                            , std_err = UseHandle hremote}
    (Just hin, _, _, ph) <- createProcess cproc
    let z3 = Z3Session { z3q     = SMTQuery structs [] funcs []
                       , z3rel   = rels
                       , z3hto   = hin
                       , z3hfrom = hlocal
                       , z3hp    = ph}
    z3checkph z3
    z3send z3 $ text "(set-option :fixedpoint.engine datalog)"
    mapM_ (z3req z3 . smtpp (z3q z3)) structs
    mapM_ (z3req z3 . smtpp (z3q z3)) funcs
    mapM_ (z3req z3 . smtpp (z3q z3)) rels
    return Session { addRule          = z3AddRule          z3
                   , addGroundRule    = z3AddGroundRule    z3
                   , removeGroundRule = z3RemoveGroundRule z3
                   , checkRelationSAT = z3CheckRelationSAT z3
                   , enumRelation     = z3EnumRelation     z3
                   }

z3checkph :: Z3Session -> IO ()
z3checkph Z3Session{..} = do
    mexit <- getProcessExitCode z3hp
    maybe (return ()) (fail . ("z3 closed unexpectedly; exit code: " ++) . show) mexit

z3req :: Z3Session -> Doc -> IO String
z3req Z3Session{..} txt = do 
    let str = render txt
    let uuid = "18b33e3d-a978-48ba-b49d-a64d232500ba"
    putStrLn $ "z3req " ++ str
    hPutStr z3hto str
    hPutStr z3hto $ "(echo \"" ++ uuid ++ "\")"
    hFlush z3hto
    let readResp :: IO [String]
        readResp = do l <- hGetLine z3hfrom
                      if l == uuid
                         then return []
                         else (liftM (l:)) readResp
    res <- (liftM $ intercalate "\n") readResp
    putStrLn $ "z3resp: " ++ res
    return res

z3send :: Z3Session -> Doc -> IO ()
z3send z3 txt = do res <- z3req z3 txt
                   when (res /= "") $ fail $ "Z3 returned unexpected response: " ++ res

z3call :: Z3Session -> Doc -> P.Parsec String () a -> IO a
z3call z3 txt parser = do
    res <- z3req z3 txt
    case P.parse parser "" res of
         Left e  -> fail $ "Error parsing Z3 output: " ++ 
                           "\nsolver input: " ++ render txt ++
                           "\nsolver output: " ++ res ++
                           "\nparser error: "++ show e
         Right x -> return x
                    {-trace "solver input: " 
                    $ trace (render quert)
                    $ trace " solver output: " 
                    $ trace out x-}

z3AddRule :: Z3Session -> Rule -> IO ()
z3AddRule z3 rule = z3send z3 $ smtpp (z3q z3) rule

z3AddGroundRule :: Z3Session -> GroundRule -> IO ()
z3AddGroundRule z3 rule = z3send z3 $ smtpp (z3q z3) rule

z3RemoveGroundRule :: Z3Session -> String -> RuleId -> IO ()
z3RemoveGroundRule z3 rel i = z3send z3 $ parens $ pp "rule" <+> (parens $ ppDisRelName rel <+> (text $ show i))

z3CheckRelationSAT :: Z3Session -> String -> IO Bool
z3CheckRelationSAT z3 rel = do
    res <- z3req z3 $ parens $ pp "query" <+> ppRelName rel <+> pp ":print-certificate false"
    case res of
         "sat"    -> return True
         "unsat"  -> return False
         str      -> fail $ "Z3 returned unexpected status: " ++ show str

z3EnumRelation :: Z3Session -> String -> IO [Assignment]
z3EnumRelation z3 rel = do 
    let parser = do res <- satresParser
                    case res of
                         True  -> let ?q = (z3q z3) in expr2Assignments z3 rel <$> exprParser Nothing
                         False -> return []
    z3call z3 (parens $ pp "query" <+> ppRelName rel <+> pp ":print-certificate true") parser

expr2Assignments :: Z3Session -> String -> Expr -> [Assignment]
expr2Assignments _  _   (EBool False)      = []
expr2Assignments z3 rel (EBinOp Or e1 e2)  = expr2Assignments z3 rel e1 ++ expr2Assignments z3 rel e2
expr2Assignments z3 rel e@(EBinOp And _ _) = [expr2Assignment relArgs e M.empty]
    where Relation{..} = fromJust $ find ((==rel) . name) (z3rel z3)
expr2Assignments  _  _   e                  = error $"Z3Datalog.expr2Assignment " ++ show e

expr2Assignment :: [Var] -> Expr -> Assignment -> Assignment
expr2Assignment []      _                                a = a
expr2Assignment (f:fs)  (EBinOp And (EBinOp Eq _ val) e) a = expr2Assignment fs e (M.insert (name f) val a)
expr2Assignment [f]     val                              a = M.insert (name f) val a
expr2Assignment fs      val                              _ = error $ "Z3Datalog.expr2Assignment " ++ show fs ++ " " ++ show val

