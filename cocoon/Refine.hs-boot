module Refine where

import qualified Data.Graph.Inductive as G

import Syntax
 
funcGraph :: Refine -> G.Gr String ()
refineStructs :: Refine -> [Type]
refineIsMulticast :: Maybe Refine -> Refine -> String -> Bool
refineIsDeterministic :: Maybe Refine -> Refine -> String -> Bool
refineRelsSorted :: Refine -> [Relation]
refinePortRels :: Refine -> [Relation]
refineSwitchRels :: Refine -> [Relation]
refinePortRoles :: Refine -> [(Role, Role, Relation)]
