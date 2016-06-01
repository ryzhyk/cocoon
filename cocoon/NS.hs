{-# LANGUAGE RecordWildCards, FlexibleContexts #-}

module NS(lookupType, checkType, getType,
          lookupFunc, checkFunc, getFunc,
          lookupVar, checkVar, getVar,
          lookupKey, checkKey, getKey,
          lookupRole, checkRole, getRole,
          lookupNode, checkNode, getNode,
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

lookupVar :: ECtx -> String -> Maybe Field
lookupVar (CtxAssume Assume{..}) n = find ((==n) . name) assVars
lookupVar (CtxFunc Function{..}) n = find ((==n) . name) funcArgs
lookupVar ctx                    n = find ((==n) . name) $ roleKeys rl ++ roleLocals rl ++ ctxForkVars ctx
    where rl = ctxRole ctx

checkVar :: (MonadError String me) => Pos -> ECtx -> String -> me Field
checkVar p c n = case lookupVar c n of
                      Nothing -> err p $ "Unknown variable: " ++ n
                      Just v  -> return v

getVar :: ECtx -> String -> Field
getVar c n = fromJust $ lookupVar c n

lookupKey :: Role -> String -> Maybe Field
lookupKey rl n = find ((==n) . name) $ roleKeys rl

checkKey :: (MonadError String me) => Pos -> Role -> String -> me Field
checkKey p rl n = case lookupKey rl n of
                       Nothing -> err p $ "Unknown key: " ++ n
                       Just k  -> return k

getKey :: Role -> String -> Field
getKey rl n = fromJust $ lookupKey rl n

lookupNode :: Refine -> String -> Maybe Node
lookupNode Refine{..} n = find ((==n) . name) refineNodes

checkNode :: (MonadError String me) => Pos -> Refine -> String -> me Node
checkNode p r n = case lookupNode r n of
                        Nothing -> errR r p $ "Unknown switch: " ++ n
                        Just sw -> return sw

getNode :: Refine -> String -> Node
getNode r n = fromJust $ lookupNode r n
