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

-- Datalog implementation on top of the differential Dataflow library:

{-# LANGUAGE ImplicitParams, RecordWildCards, OverloadedStrings, ScopedTypeVariables #-}

module Datalog.DataflogSession (newSession) where

import qualified Data.Aeson as J
import Data.Scientific
import qualified Data.HashMap.Lazy as H
import qualified Data.Vector as V
import Control.Monad.Except
import System.IO
import System.Process
import Data.Attoparsec.ByteString
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString as BSS
import Data.Text (pack, unpack)
import Data.Maybe
import Data.List


import SMT.SMTSolver
import Datalog.Datalog
import Name

err :: String -> IO a
err = error --throwError . strMsg

valToJSON :: (?q::SMTQuery) => Expr -> J.Value
valToJSON (EBool b)              = J.Bool b
valToJSON (EBit w i) | w <= 64   = J.Number $ scientific i 0
                     | otherwise = J.String $ pack $ show i
valToJSON (EInt i)               = J.String $ pack $ show i
valToJSON (EString s)            = J.String $ pack s
valToJSON (EStruct c as)         = J.Object $ H.singleton (pack c) 
                                   $ J.Object $ H.fromList $ map (\(f,a) -> (pack $ name f, valToJSON a)) $ zip fs as
    where Struct _ fs = getConsStruct ?q c
valToJSON e                      = error $ "DataflogSession.valToJSON " ++ show e

valFromJSON :: (?q::SMTQuery) => Type -> J.Value -> IO Expr
valFromJSON TBool       (J.Bool b)      = return $ EBool b
valFromJSON TInt        (J.String s)    = case reads $ unpack s of
                                               []        -> err $ "invalid integer value " ++ unpack s
                                               ((i,_):_) -> return $ EInt i
valFromJSON TString     (J.String s)    = return $ EString $ unpack s
valFromJSON (TBit w)    (J.String s)    = case reads $ unpack s of
                                               []        -> err $ "invalid integer value " ++ unpack s
                                               ((i,_):_) -> return $ EBit w i
valFromJSON (TBit w)    (J.Number n)    = case floatingOrInteger n of
                                               Left (_::Double) -> err $ "not an integral value " ++ show n
                                               Right i          -> return $ EBit w i
valFromJSON (TStruct s) (J.Object o)    = 
    case H.toList o of
         [(c, J.Object v)] -> case lookupConsStruct ?q (unpack c) of
                                   Nothing -> err $ "Invalid constructor " ++ unpack c 
                                   Just s' | name s' /= s -> err $ "Constructor " ++ unpack c ++ " does not match expected type " ++ s
                                           | otherwise    -> do let Constructor _ as = getConstructor ?q $ unpack c
                                                                fs <- mapM (\a -> case H.lookup (pack $ name a) v of
                                                                                       Nothing -> err $ "Field " ++ name a ++ " is missing in JSON"
                                                                                       Just v' -> valFromJSON (varType a) v') as
                                                                return $ EStruct (unpack c) fs
         _        -> err $ "Invalid struct " ++ show o
valFromJSON t           v               = err $ "Cannot decode JSON value " ++ show v ++ " as " ++ show t


factToJSON :: (?q::SMTQuery) => Fact -> J.Value
factToJSON Fact{..} = 
    case factArgs of
         [a] -> J.Object $ H.singleton (pack factRel) $ valToJSON a
         _   -> J.Object $ H.singleton (pack factRel) $ J.Array $ V.fromList $ map valToJSON factArgs

factFromJSON :: DFSession -> String -> J.Value -> IO Fact
factFromJSON DFSession{..} rname val = do
    let Relation{..} = fromJust $ find ((== rname) . name) dfRels
    let ?q = dfQ
    case relArgs of
         [a] -> do arg <- valFromJSON (varType a) val
                   return $ Fact rname [arg]
         _   -> case val of
                     J.Array vals -> do when (V.length vals /= length relArgs) $ err $ "Tuple " ++ show val ++ " has incorrect number of arguments"
                                        args <- mapM (\(a,v) -> valFromJSON (varType a) v) $ zip relArgs (V.toList vals)
                                        return $ Fact rname args
                     _            -> err $ "Invalid tuple: " ++ show val
    

data DFSession = DFSession { dfQ     :: SMTQuery
                           , dfRels  :: [Relation]
                           , dfHTo   :: Handle
                           , dfHFrom :: Handle
                           , dfHP    :: ProcessHandle
                           }

data Request = ReqAdd    Fact
             | ReqRemove Fact
             | ReqCheck  String
             | ReqEnum   String

requestToJSON :: (?q::SMTQuery) => Request -> J.Value
requestToJSON (ReqAdd f)    = J.Object $ H.singleton "add" $ factToJSON f
requestToJSON (ReqRemove f) = J.Object $ H.singleton "del" $ factToJSON f
requestToJSON (ReqCheck r)  = J.Object $ H.singleton "chk" $ J.String $ pack r
requestToJSON (ReqEnum r)   = J.Object $ H.singleton "enm" $ J.String $ pack r

respUnwrap :: J.Value -> IO J.Value
respUnwrap v = case v of
                    J.Object vs -> case H.toList vs of
                                        [("err", J.String str)] -> err $ "Dataflog failed to process query: " ++ unpack str
                                        [("ok", v')]            -> return v'
                                        _                       -> err $ "Invalid Dataflog response: " ++ show v
                    _           -> err $ "Invalid Dataflog response: " ++ show v

newSession :: FilePath -> [Struct] -> [Function] -> [Relation] -> IO Session
newSession path structs funs rels = do
    -- Run dataflog program
    (hlocal, hremote) <- createPipe
    let cproc = (proc path []){ std_out = UseHandle hremote
                              , std_in  = CreatePipe
                              , std_err = UseHandle hremote}
    (Just hin, _, _, ph) <- createProcess cproc
    let df = DFSession { dfQ     = SMTQuery structs [] funs []
                       , dfRels  = rels
                       , dfHTo   = hin
                       , dfHFrom = hlocal
                       , dfHP    = ph
                       }
    checkph df
    return $ Session { addFact          = dfAddFact          df
                     , removeFact       = dfRemoveFact       df
                     , checkRelationSAT = dfCheckRelationSAT df
                     , enumRelation     = dfEnumRelation     df
                     , closeSession     = dfCloseSession     df
                     }

checkph :: DFSession -> IO ()
checkph DFSession{..} = do
    mexit <- getProcessExitCode dfHP
    maybe (return ()) (fail . ("Dataflog process terminated unexpectedly; exit code: " ++) . show) mexit

req :: (J.ToJSON a) => DFSession -> a -> IO J.Value
req df@DFSession{..} v = do
    checkph df
    let json = J.encode v
    BSL.hPutStr stderr $ "> "
    BSL.hPutStr stderr $ json
    BSL.hPutStr stderr $ "\n"
    BSL.hPut dfHTo json
    hFlush dfHTo
    BSS.hPutStr stderr "< "
    res <- parseWith (hGetSome' dfHFrom 4096) J.json ""
    BSS.hPutStr stderr "\n"
    case res of
         Done _ r   -> return r
         Fail _ _ e -> error $ "Failed to parse response from the Dataflog process: " ++ e
         Partial _  -> error "Incomplete response received from the Dataflog process"

hGetSome' :: Handle -> Int -> IO BSS.ByteString
hGetSome' h i = do
    s <- BSS.hGetSome h i
    BSS.hPutStr stderr s
    return s

dfAddFact :: DFSession -> Fact -> IO ()
dfAddFact df fact = do
    let ?q = dfQ df
    let json = requestToJSON $ ReqAdd fact
    resp <- req df json
    _ <- respUnwrap resp
    return ()

dfRemoveFact :: DFSession -> Fact -> IO ()
dfRemoveFact df fact = do
    let ?q = dfQ df
    let json = requestToJSON $ ReqRemove fact
    resp <- req df json
    _ <- respUnwrap resp
    return ()

dfCheckRelationSAT :: DFSession -> String -> IO Bool
dfCheckRelationSAT df rel = do 
    let ?q = dfQ df
    let json = requestToJSON $ ReqCheck rel
    resp <- req df json
    status <- respUnwrap resp
    case status of
         J.Bool b -> return b
         _        -> err $ "Dataflog returned invalid status: " ++ show status

dfEnumRelation :: DFSession -> String -> IO [Fact]
dfEnumRelation df rel = do
    let ?q = dfQ df
    let json = requestToJSON $ ReqEnum rel
    resp <- req df json
    res <- respUnwrap resp
    case res of
         J.Array facts -> mapM (factFromJSON df rel) $ V.toList facts
         _             -> err $ "Dataflog returned invalid value: " ++ show res

dfCloseSession :: DFSession -> IO ()
dfCloseSession df = do
   terminateProcess $ dfHP df
   _ <- waitForProcess $ dfHP df
   return () 
