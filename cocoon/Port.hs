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

{-# LANGUAGE RecordWildCards #-}

module Port ( portSendsToPortsRec
            , portUsesRels
            , portSwitchRel) where

import Data.List
import Data.Maybe

import Syntax
import Expr
import NS

portSendsToPortsRec :: Refine -> [DirPort] -> DirPort -> [DirPort]
portSendsToPortsRec r ports port = portSendsToPortsRec' r ports [] [port]

portSendsToPortsRec' :: Refine -> [DirPort] -> [DirPort] -> [DirPort] -> [DirPort]
portSendsToPortsRec' _ _     found [] = found
portSendsToPortsRec' r ports found (p:frontier) = portSendsToPortsRec' r ports found' frontier'
    where dst = maybe [] (exprSendsToPorts r . fromJust . funcDef) $ getPortDef r p
          new = dst \\ found
          found' = new ++ found
          frontier' = union frontier $ intersect ports new

portUsesRels :: Refine -> SwitchPort -> [String]
portUsesRels r SwitchPort{..} = nub $ portRel : exprUsesRels r (fromJust $ funcDef $ getFunc r portIn)

portSwitchRel :: Refine -> SwitchPort -> String
portSwitchRel r p = swrel
    where rel = getRelation r $ portRel p
          [swrel] = map constrForeign $ filter ((== [eVar "switch"]) . constrFields) $ filter isForeignKey $ relConstraints rel
