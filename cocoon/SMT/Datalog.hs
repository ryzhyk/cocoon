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

-- Generic interface to a Datalog engine

{-# LANGUAGE RecordWildCards #-}

module SMT.Datalog( DatalogEngine(..)
                  , Relation(..)
                  , Rule(..)
                  , RuleId
                  , GroundRule(..)
                  , Session(..)) where

import Data.Int

import Name
import SMT.SMTSolver

data Relation = Relation { relName :: String 
                         , relArgs :: [Var]
                         }

instance WithName Relation where
    name = relName

data Rule = Rule { ruleVars :: [Var]
                 , ruleHead :: Expr
                 , ruleBody :: Expr
                 , ruleId   :: RuleId -- get rid of this
                 }

data GroundRule = GroundRule { gruleRel  :: String
                             , gruleArgs :: [Expr]
                             , gruleId   :: RuleId}

type RuleId = Int64

data Session = Session {
    addRule             :: Rule             -> IO (),
    addGroundRule       :: GroundRule       -> IO (),
    removeGroundRule    :: String -> RuleId -> IO (),
    checkRelationSAT    :: String           -> IO Bool,
    enumRelation        :: String           -> IO [Assignment]
}

data DatalogEngine = DatalogEngine {newSession :: [Struct] -> [Function] -> [Relation] ->  IO Session}
