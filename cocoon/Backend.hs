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


module Backend where

import qualified Data.Map as M

import Syntax
import IR.Registers

newtype FName = FName String deriving (Eq, Ord)

type FieldMap = M.Map String FName

data StructReify = StructReify { reifyWidth :: M.Map String Int
                               , reifyCons  :: M.Map String Integer
                               }

data Backend = Backend { backendRegisters :: RegisterFile  -- Backend's register file
                       , backendPktType   :: Type          -- Packet type assumed by backend
                       , backendStructs   :: StructReify 
                       }
