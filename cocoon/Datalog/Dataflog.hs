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

-- Datalog implementation on top of the differential Dataflow library:


module Datalog.Dataflog ( ) where

-- structs

-- rule graph
-- DAG of connected components 


mkRule 

    rel.filter({-constructors-}).map({-decompose-}).map({-leave outcome vars only-})
    
    (.....).join_map(rel.filter({-constructors-}).map({-decompose, pivot-}), |{- lhs vars, rel vars -} | ({- outcome vars -}) )

    
    
    -- left-to-right, adding one predicate at a time
        -- filter() based on constructors
        -- compute join variables: intersection of variables on the left with variable in the new predicate 
        -- compute outcome variables: intersection of variables on the left of the join with
            -- variables on the right and in the head of the rule
        
        -- map: pivot lhs relation (decomposing constructors into fields)
        -- map: pivot atom
        -- join_map
