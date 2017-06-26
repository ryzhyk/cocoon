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

{-# LANGUAGE RecordWildCards, LambdaCase, ScopedTypeVariables, ImplicitParams, OverloadedStrings, PackageImports #-}

module CLI (controllerCLI) where

import "daemons" System.Daemon
import qualified Data.ByteString.Char8 as BS
import System.Console.Haskeline
import Control.Monad.Trans


controllerCLI :: FilePath -> Int -> IO ()
controllerCLI hist port = runInputT defaultSettings{historyFile = Just hist} loop
    where loop :: InputT IO ()
          loop = do
              minput <- getInputLine "> "
              case minput of
                   Nothing     -> loop
                   Just "exit" -> return ()
                   Just cmd    -> do
                       resp::(Maybe BS.ByteString) <- lift $ runClient "localhost" port (BS.pack cmd)
                       case resp of
                            Nothing -> do outputStrLn $ "Unable to connect to cocoon controller.  Is the controller running on port " ++ show port ++ "?"
                                          return ()
                            Just r  -> do outputStrLn $ BS.unpack r 
                                          loop
