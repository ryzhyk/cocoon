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
import Data.String
import Data.List
import Data.Maybe
import Control.Exception
import Control.Monad

import Util
import Syntax
import Refine
import NS
import Relation
import Name
import Type
import qualified SQL
import qualified SMT.Datalog   as DL
import qualified SMT.Z3Datalog as DL
import qualified SMT           as SMT
import qualified SMT.SMTSolver as SMT

data ControllerState = ControllerState {
    ctlDL           :: DL.Session,
    ctlConstraints  :: [(Relation, [DL.Relation])],
    ctlDB           :: PG.Connection
}

data Violation = Violation Relation Constraint SMT.Assignment

instance Show Violation where
    show (Violation rel c asn) = "row " ++ show asn ++ " violates constraint " ++ show c ++ " on table " ++ name rel

controllerLoop :: String -> Refine -> IO ()
controllerLoop dbname r = do
    let ?r = r
    db <- PG.connectPostgreSQL $ BS.pack $ "dbname=" ++ dbname
    putStrLn "Connected to database"
    (dl, constr) <- startDLSession
    let ?s = ControllerState dl constr db
    populateDB
    -- event loop
    PG.close db
    putStrLn "Disconnected"

startDLSession :: (?r::Refine) => IO (DL.Session, [(Relation, [DL.Relation])])
startDLSession = do
    let rels = refineRelsSorted ?r
    let funcs = map (getFunc ?r) $ nub $ concatMap (relFuncsRec ?r) rels
    let funcs' = map SMT.func2SMT funcs
    let structs = map (\t -> SMT.struct2SMT (name t) $ typeCons $ fromJust $ tdefType t)
                  $ nub $ map (structTypeDef ?r . typ' ?r) 
                  $ filter (\case 
                             TStruct _ _ -> True
                             _           -> False) 
                  $ typeSort ?r $ nub $ concatMap (relTypes ?r) rels
    let dlrels = zip rels $ map SMT.rel2DL rels
    let (allrels, allrules) = unzip $ concatMap ( (\(mrel,crels) -> mrel:(concat crels)) . snd) dlrels
    dl@DL.Session{..} <- (DL.newSession DL.z3DatalogEngine) structs funcs' allrels
    mapM_ addRule $ concat allrules
    return (dl, map (mapSnd (map (fst . last) . snd)) dlrels)


populateDB :: (?r::Refine, ?s::ControllerState) => IO ()
populateDB = do 
    PG.withTransaction (ctlDB ?s) $ readDB
    validateConstraints
    

validateConstraints :: (?s::ControllerState) => IO ()
validateConstraints = do
    violations <- checkConstraints 
    let e = concatMap (("Integrity violation: " ++) . show) violations
    throw $ AssertionFailed e

checkConstraints :: (?s::ControllerState) => IO [Violation]
checkConstraints = 
    (liftM concat) 
    $ mapM (\(rel, dlrels) -> do assigns <- mapM (DL.enumRelation (ctlDL ?s) . name) dlrels
                                 return $ concatMap (\(asns, constr) -> map (Violation rel constr) asns) 
                                        $ filter (not . null . fst)
                                        $ zip assigns (relConstraints rel)) 
    $ ctlConstraints ?s
   
readDB :: (?r::Refine, ?s::ControllerState) => IO ()
readDB = mapM_ (\rel -> do rows <- SQL.readTable (ctlDB ?s) rel
                           mapM_ (\(idx, args) -> (DL.addGroundRule $ ctlDL ?s) 
                                                  $ DL.GroundRule (name rel) (map (SMT.expr2SMT CtxRefine) args) idx) rows) 
         $ filter (not . relIsView) $ refineRels ?r


