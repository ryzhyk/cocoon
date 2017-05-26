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

{-# LANGUAGE RecordWildCards #-}

module SMT.Z3Datalog(z3DatalogEngine) where

import Text.PrettyPrint
import System.Process
import GHC.IO.Handle

import SMT.Datalog
import SMT.SMTLib2
import SMT.SMTSolver

data Z3Session = Z3Session { z3q     :: SMTQuery
                           , z3hto   :: Handle
                           , z3hfrom :: Handle
                           , z3hp    :: ProcessHandle}
z3DatalogEngine = DatalogEngine {newSession = z3NewSession}

z3NewSession :: [Struct] -> [Function] -> IO Session
z3NewSession structs funcs = do
    (hlocal, hremote) <- createPipe
    let cproc = (proc "z3" ["-smt2", "-in"]){ std_out = UseHandle hremote
                                            , std_in  = CreatePipe
                                            , std_err = UseHandle hremote}
    (Just hin, _, _, ph) <- createProcess cproc
    mexit <- getProcessExitCode ph
    case mexit of
         Nothing -> putStrLn "z3 is running"
         Just e  -> do putStrLn $ "z3 terminated with exit code " ++ show e
    let z3 = Z3Session { z3q     = SMTQuery structs [] funcs []
                       , z3hto   = hin
                       , z3hfrom = hlocal
                       , z3hp    = ph}
    z3send z3 $ text "(set-option :fixedpoint.engine datalog)"
    mapM_ (z3send z3 . smtpp (z3q z3)) structs
    mapM_ (z3send z3 . smtpp (z3q z3)) funcs
    return Session { addRelation      = z3AddRelation      z3
                   , addRule          = z3AddRule          z3
                   , addGroundRule    = z3AddGroundRule    z3
                   , removeGroundRule = z3RemoveGroundRule z3
                   , checkRelationSAT = z3CheckRelationSAT z3
                   , enumRelation     = z3EnumRelation     z3
                   }

z3send :: Z3Session -> Doc -> IO ()
z3send Z3Session{..} txt = do 
    let str = render txt
    putStrLn $ "z3send " ++ str
    hPutStr z3hto str

z3AddRelation :: Z3Session -> Relation -> IO ()
z3AddRelation z3 rel = z3send z3 $ smtpp (z3q z3) rel

z3AddRule :: Z3Session -> Rule -> IO ()
z3AddRule z3 rule = z3send z3 $ smtpp (z3q z3) rule

z3AddGroundRule :: Z3Session -> GroundRule -> IO ()
z3AddGroundRule z3 rule = z3send z3 $ smtpp (z3q z3) rule

z3RemoveGroundRule    :: Z3Session -> RuleId               -> IO ()
z3RemoveGroundRule = undefined

z3CheckRelationSAT :: Z3Session -> String               -> IO Bool
z3CheckRelationSAT = undefined

z3EnumRelation        :: Z3Session -> String               -> IO [Assignment]
z3EnumRelation = undefined
