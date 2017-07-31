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
module Role ( roleSendsToRolesRec
            , roleIsInPort
            , roleIsOutPort
            , portRoleSwitch) where

import Data.List
import Data.Tuple.Select

import Name
import Syntax
import Expr
import NS
import {-# SOURCE #-} Refine

roleSendsToRolesRec :: Refine -> [String] -> String -> [String]
roleSendsToRolesRec r roles role = roleSendsToRolesRec' r roles [] [role]

roleSendsToRolesRec' :: Refine -> [String] -> [String] -> [String] -> [String]
roleSendsToRolesRec' _ _     found [] = found
roleSendsToRolesRec' r roles found (rl:frontier) = roleSendsToRolesRec' r roles found' frontier'
    where dst = exprSendsToRoles r $ roleBody $ getRole r rl
          new = dst \\ found
          found' = new ++ found
          frontier' = union frontier $ intersect roles new

roleIsInPort :: Refine -> String -> Bool
roleIsInPort r rl = elem rl $ map (name . sel1) $ refinePortRoles r

roleIsOutPort :: Refine -> String -> Bool
roleIsOutPort r rl = elem rl $ map (name . sel2) $ refinePortRoles r

portRoleSwitch :: Refine -> Role -> String
portRoleSwitch r rl = swrole
    where rel = getRelation r $ roleTable rl
          [swrole] = map constrForeign $ filter ((== [eVar "switch"]) . constrFields) $ filter isForeignKey $ relConstraints rel
