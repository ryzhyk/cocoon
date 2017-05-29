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

{-# LANGUAGE RecordWildCards, LambdaCase, ScopedTypeVariables, ImplicitParams, OverloadedStrings #-}

module Controller (controllerLoop) where

import qualified Database.PostgreSQL.Simple as PG
import qualified Data.ByteString.Char8 as BS
import qualified Data.Aeson as JSON
import Data.String
import Data.List
import Data.Maybe

import Syntax
import Refine
import NS
import Relation
import Name
import Type
import qualified SMT.Datalog   as DL
import qualified SMT.Z3Datalog as DL
import qualified SMT as SMT

controllerLoop :: String -> Refine -> IO ()
controllerLoop dbname r = do
    db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ dbname
    let ?db = db
    let ?r = r
    putStrLn "Connected to database"
    let rels = refineRelsSorted r
    let funcs = map (getFunc r) $ nub $ concatMap (relFuncsRec r) rels
    let funcs' = map SMT.func2SMT funcs
    let structs = map (\t -> SMT.struct2SMT (name t) $ typeCons $ fromJust $ tdefType t)
                  $ nub $ map (structTypeDef r . typ' r) 
                  $ filter (\case 
                             TStruct _ _ -> True
                             _           -> False) 
                  $ typeSort r $ nub $ concatMap (relTypes r) rels
    let dlrels = map SMT.rel2DL rels
    DL.Session{..} <- (DL.newSession DL.z3DatalogEngine) structs funcs' (map fst dlrels)
    mapM_ ((\rules -> mapM_ addRule rules) . snd) dlrels
    -- populate datalog with base tables
    PG.withTransaction db $ do readDB r
                               --subscribe db r

    -- create view relations and rules
    -- event loop

    PG.close db
    putStrLn "Disconnected"
    

readDB :: (?db :: PG.Connection) => Refine -> IO ()
readDB r = mapM_ readTable $ filter (not . relIsView) $ refineRels r    

readTable :: (?db :: PG.Connection) => Relation -> IO ()
readTable rel@Relation{..} = do
    let q = "select to_json(" ++ relName ++ ") from " ++ relName
    PG.forEach_ ?db (fromString q) (\(x::[JSON.Value]) -> mapM_ (putStrLn . show) x )
