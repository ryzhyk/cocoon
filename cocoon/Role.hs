module Role (roleSendsToRolesRec) where

import Data.List

import Syntax
import Statement
import NS

roleSendsToRolesRec :: Refine -> [String] -> String -> [String]
roleSendsToRolesRec r roles role = roleSendsToRolesRec' r roles [] [role]

roleSendsToRolesRec' :: Refine -> [String] -> [String] -> [String] -> [String]
roleSendsToRolesRec' _ _     found [] = found
roleSendsToRolesRec' r roles found (rl:frontier) = roleSendsToRolesRec' r roles found' frontier'
    where dst = statSendsToRoles $ roleBody $ getRole r rl
          new = dst \\ found
          found' = new ++ found
          frontier' = union frontier $ intersect roles new
