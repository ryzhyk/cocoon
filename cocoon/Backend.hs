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

{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Backend where

import qualified Data.Map as M
import Control.Monad.Except
import qualified Data.ByteString as B

import Syntax
import qualified IR.IR as IR
import qualified Datalog.Datalog as DL

-- reifyWidth - Number of bits to represent tags of tagged union (struct) types,
-- reifyCons  - Backend-specific encoding of constructor values 
data StructReify = StructReify { reifyWidth :: M.Map String Int
                               , reifyCons  :: M.Map String Integer
                               }

type PktCB = String -> [Expr] -> B.ByteString -> IO [(B.ByteString, Int)]

data Backend p = Backend { backendStructs      :: StructReify
                         , backendValidate     :: forall me . (MonadError String me) => Refine -> me ()
                         , backendPrecompile   :: forall me . (MonadError String me) => FilePath -> Refine -> me p
                         , backendStart        :: Refine -> p -> PktCB -> IO ()
                         , backendBuildSwitch  :: FilePath -> Refine -> Switch -> DL.Fact -> p -> IR.DB -> IO ()
                         , backendUpdateSwitch :: FilePath -> Refine -> Switch -> DL.Fact -> p -> IR.Delta -> IO ()
                         , backendResetSwitch  :: FilePath -> Refine -> Switch -> DL.Fact -> IO ()
                         , backendStop         :: IO ()
                         }
