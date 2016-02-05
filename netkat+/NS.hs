{-# LANGUAGE RecordWildCards, FlexibleContexts #-}

module NS(lookupType, checkType, getType,
          lookupFunc, checkFunc, getFunc,
          lookupKey, checkKey, getKey,
          lookupRole, checkRole, getRole,
          lookupSwitch, checkSwich, getSwitch,
          packetTypeName) where

import Data.List
import Control.Monad.Except
import Data.Maybe

import Syntax
import Name
import Util
import Pos

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


lookupKey :: Role -> String -> Maybe Field
lookupKey Role{..} n = find ((==n) . name) roleKeys

checkKey :: (MonadError String me) => Pos -> Role -> String -> me Field
checkKey p r n = case lookupKey r n of
                      Nothing -> err p $ "Unknown key: " ++ n
                      Just k  -> return k

getKey :: Role -> String -> Field
getKey r n = fromJust $ lookupKey r n

lookupSwitch :: Refine -> String -> Maybe Switch
lookupSwitch Refine{..} n = find ((==n) . name) refineSwitches

checkSwich :: (MonadError String me) => Pos -> Refine -> String -> me Switch
checkSwich p r n = case lookupSwitch r n of
                        Nothing -> errR r p $ "Unknown switch: " ++ n
                        Just sw -> return sw

getSwitch :: Refine -> String -> Switch
getSwitch r n = fromJust $ lookupSwitch r n
