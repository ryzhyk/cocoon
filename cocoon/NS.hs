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
{-# LANGUAGE RecordWildCards, FlexibleContexts #-}

module NS(lookupType, checkType, getType,
          lookupFunc, checkFunc, getFunc,
          lookupVar, checkVar, getVar,
          --lookupLocalVar, checkLocalVar, getLocalVar,
          lookupRole, checkRole, getRole,
          lookupNode, checkNode, getNode,
          lookupConstructor, checkConstructor, getConstructor,
          lookupRelation, checkRelation, getRelation,
          --lookupBuiltin, checkBuiltin, getBuiltin,
          packetTypeName) where

import Data.List
import Control.Monad.Except
import Data.Maybe

import Syntax
import Name
import Util
import Pos
--import {-# SOURCE #-}Builtins

packetTypeName = "Packet"

lookupType :: Refine -> String -> Maybe TypeDef
lookupType Refine{..} n = find ((==n) . name) refineTypes

checkType :: (MonadError String me) => Pos -> Refine -> String -> me TypeDef
checkType p r n = case lookupType r n of
                       Nothing -> errR r p $ "Unknown type: " ++ n
                       Just t  -> return t

getType :: Refine -> String -> TypeDef
getType r n = fromJust $ lookupType r n


lookupFunc :: Refine -> String -> Maybe Function
lookupFunc Refine{..} n = find ((==n) . name) refineFuncs

checkFunc :: (MonadError String me) => Pos -> Refine -> String -> me Function
checkFunc p r n = case lookupFunc r n of
                       Nothing -> errR r p $ "Unknown function: " ++ n
                       Just f  -> return f

getFunc :: Refine -> String -> Function
getFunc r n = fromJust $ lookupFunc r n


lookupRole :: Refine -> String -> Maybe Role
lookupRole Refine{..} n = find ((==n) . name) refineRoles

checkRole :: (MonadError String me) => Pos -> Refine -> String -> me Role
checkRole p r n = case lookupRole r n of
                       Nothing -> errR r p $ "Unknown role: " ++ n
                       Just rl -> return rl

getRole :: Refine -> String -> Role
getRole r n = fromJust $ lookupRole r n

lookupVar :: Refine -> ECtx -> String -> Maybe Field
lookupVar = error "lookupVar is undefined"

checkVar :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me Field
checkVar p r c n = case lookupVar r c n of
                        Nothing -> err p $ "Unknown variable: " ++ n
                        Just v  -> return v

getVar :: Refine -> ECtx -> String -> Field
getVar r c n = fromJust $ lookupVar r c n


{-
lookupLocalVar :: Role -> String -> Maybe Field
lookupLocalVar role n = find ((==n) . name) $ roleLocals role

checkLocalVar :: (MonadError String me) => Pos -> Role -> String -> me Field
checkLocalVar p rl n = case lookupLocalVar rl n of
                            Nothing -> err p $ "Unknown local variable: " ++ n
                            Just v  -> return v

getLocalVar :: Role -> String -> Field
getLocalVar rl n = fromJust $ lookupLocalVar rl n
-}

{-
lookupKey :: Role -> String -> Maybe Field
lookupKey rl n = find ((==n) . name) $ roleKeys rl

checkKey :: (MonadError String me) => Pos -> Role -> String -> me Field
checkKey p rl n = case lookupKey rl n of
                       Nothing -> err p $ "Unknown key: " ++ n
                       Just k  -> return k

getKey :: Role -> String -> Field
getKey rl n = fromJust $ lookupKey rl n
-}


lookupNode :: Refine -> String -> Maybe Node
lookupNode Refine{..} n = find ((==n) . name) refineNodes

checkNode :: (MonadError String me) => Pos -> Refine -> String -> me Node
checkNode p r n = case lookupNode r n of
                        Nothing -> errR r p $ "Unknown switch: " ++ n
                        Just sw -> return sw

getNode :: Refine -> String -> Node
getNode r n = fromJust $ lookupNode r n

lookupConstructor :: Refine -> String -> Maybe Constructor
lookupConstructor = error "lookupConstructor is undefined"

checkConstructor :: (MonadError String me) => Pos -> Refine -> String -> me Constructor
checkConstructor = error "lookupConstructor is undefined"

getConstructor :: Refine -> String -> Constructor
getConstructor = error "getConstructor is undefined"

lookupRelation :: Refine -> String -> Maybe Relation
lookupRelation = error "lookupRelation is undefined"

checkRelation :: (MonadError String me) => Pos -> Refine -> ECtx -> String -> me Relation
checkRelation = error "lookupRelation is undefined"

getRelation :: Refine -> String -> Relation
getRelation = error "getRelation is undefined"



{-
lookupBuiltin :: String -> Maybe Builtin
lookupBuiltin n = find ((==n) . name) builtins

checkBuiltin :: (MonadError String me) => Pos -> String -> me Builtin
checkBuiltin p n = case lookupBuiltin n of
                        Nothing -> err p $ "Unknown builtin: " ++ n
                        Just b  -> return b

getBuiltin :: String -> Builtin
getBuiltin n = fromJust $ lookupBuiltin n
-}
