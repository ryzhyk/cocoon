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

{-# LANGUAGE OverloadedStrings, RecordWildCards, FlexibleContexts, LambdaCase, ScopedTypeVariables #-}

module OpenFlow.OVS (ovsBackend) where

import Text.PrettyPrint
import qualified Data.Map as M
import Text.Printf
import System.FilePath.Posix
import System.Process
import System.Exit
import Control.Monad
import Control.Monad.Except
import Data.List

import OpenFlow.OVSConst
import OpenFlow.OVSProtocol
import Util
import Name
import PP
import Backend
import Numeric
import Syntax
import qualified OpenFlow.OpenFlow as OF
import qualified OpenFlow.IR2OF    as OF
import qualified IR.IR             as IR
import qualified Datalog.Datalog   as DL
import qualified Datalog           as DL

ovsBackend :: Backend OF.IRSwitches
ovsBackend = Backend { backendStructs      = ovsStructReify
                     , backendValidate     = error "backendValidate not implemented"
                     , backendPrecompile   = ovsPrecompile
                     , backendStart        = ovsStart
                     , backendBuildSwitch  = ovsBuildSwitch
                     , backendUpdateSwitch = ovsUpdateSwitch
                     , backendResetSwitch  = ovsResetSwitch
                     , backendStop         = ovsStop
                     }

ovsPrecompile :: (MonadError String me) => FilePath -> Refine -> me OF.IRSwitches
ovsPrecompile workdir r = OF.precompile ovsStructReify workdir r ovsRegFile

ovsBuildSwitch :: FilePath -> Refine -> Switch -> DL.Fact -> OF.IRSwitches -> IR.DB -> IO ()
ovsBuildSwitch workdir r sw f@(DL.Fact rname _) ir db = do
    let swid = DL.factSwitchId r rname f
        E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
        cmds = OF.buildSwitch r (ir M.! name sw) db swid
    ovsResetSwitch workdir r sw f
    sendCmds workdir rname swid swaddr swname cmds


ovsUpdateSwitch :: FilePath -> Refine -> Switch -> DL.Fact -> OF.IRSwitches -> IR.Delta -> IO ()
ovsUpdateSwitch workdir r sw f@(DL.Fact rname _) ir delta = do
    let swid = DL.factSwitchId r rname f
        E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
        cmds = OF.updateSwitch r (ir M.! name sw) swid delta
    when (not $ null cmds) $ sendCmds workdir rname swid swaddr swname cmds

ovsResetSwitch :: FilePath -> Refine -> Switch -> DL.Fact -> IO ()
ovsResetSwitch _ r _ f = do
    let E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
    reset swaddr swname

-- From ovs-ofctl documentation:
-- Transactional  updates  to both flow and group tables can be made 
-- with the bundle command.  file is a text file that contains zero or 
-- more flows and groups in either Flow Syntax or Group Syntax, each 
-- line preceded by either flow or group keyword.  The flow keyword 
-- may be optionally followed by one of the keywords add, modify, 
-- modify_strict, delete, or delete_strict, of which the add  is  
-- assumed  if a bare flow is given.  Similarly, the group keyword may 
-- be optionally followed by one of the keywords add, modify, 
-- add_or_mod, delete, insert_bucket, or remove_bucket, of which the 
-- add is assumed if a bare group is given.

reset :: String -> String -> IO ()
reset swaddr swname = do
   let args = ["--protocols=OpenFlow15", "del-flows"] ++ (if swaddr == "" then [] else [swaddr]) ++ [swname]
   (code, stdo, stde) <- readProcessWithExitCode "ovs-ofctl" args ""
   when (code /= ExitSuccess) $ error $ "ovs-ofctl del-flows failed with exit code " ++ show code ++ 
                                        "\ncommand line: ovs-ofctl " ++ (intercalate " " args) ++
                                        "\noutput: " ++ stdo ++
                                        "\nstd error: " ++ stde

sendCmds :: FilePath -> String -> Integer -> String -> String -> [OF.Command] -> IO ()
sendCmds workdir swrel swid swaddr swname cmds = do
   let ofcmds = render $ vcat $ map mkCmd cmds
       fname = swrel ++ "-" ++ show swid
       f = workdir </> addExtension fname "of"
   -- write commands to file
   writeFile f ofcmds
   let args = ["--protocols=OpenFlow15", "bundle"] ++ (if swaddr == "" then [] else [swaddr]) ++ [swname, f]
   (code, stdo, stde) <- readProcessWithExitCode "ovs-ofctl" args ""
   when (code /= ExitSuccess) $ error $ "ovs-ofctl failed with exit code " ++ show code ++ 
                                        "\ncommand line: ovs-ofctl " ++ (intercalate " " args) ++
                                        "\noutput: " ++ stdo ++
                                        "\nstd error: " ++ stde ++
                                        "\nOF commands:\n" ++ ofcmds

commaCat = hcat . punctuate comma . filter (not . (==empty))

mkCmd :: OF.Command -> Doc
mkCmd (OF.AddFlow t OF.Flow{..}) = vcat
                                   $ map (\m -> "flow add" <+>
                                                commaCat [ "table=" <> pp t
                                                         , "priority=" <> pp flowPriority
                                                         , commaCat m
                                                         , "actions=" <> (commaCat $ map mkAction flowActions)])
                                   $ allComb $ map mkMatch flowMatch
mkCmd (OF.DelFlow t p ms)        = vcat 
                                   $ map (\m -> "flow delete_strict" <+>
                                                commaCat [ "table=" <> pp t
                                                         , "priority=" <> pp p
                                                         , commaCat m])
                             $ allComb $ map mkMatch ms
mkCmd (OF.AddGroup OF.Group{..}) = "group add" <+>
                                   commaCat [ "group_id=" <> pp groupId
                                            , "type=" <> pp groupType
                                            , commaCat $ map (("bucket=" <>) . mkBucket) groupBuckets]
mkCmd (OF.DelGroup gid)          = "group delete" <+> "group_id=" <> pp gid
mkCmd (OF.AddBucket gid b)       = "group insert_bucket" <+> 
                                   "group_id=" <> pp gid <> comma <>
                                   "bucket=" <> mkBucket b
mkCmd (OF.DelBucket gid bid)     = "group remove_bucket" <+> 
                                   "group_id=" <> pp gid <> comma <>
                                   "bucket_id=" <> pp bid

mkMatch :: OF.Match -> [Doc]
mkMatch OF.Match{..} = map (\m -> pp n <> "=" <> mkVal attrFormat matchVal <> m) masks
    where n = case M.lookup (OF.fieldName matchField) matchMap  of
                   Nothing -> error $ "OVS.mkMatch: unknown field " ++ OF.fieldName matchField
                   Just x  -> x
          Attributes{..} = matchAttributes M.! n
          masks = case matchMask of
                       Nothing                             -> [empty]
                       Just m | OF.isFullMask matchField m -> [empty]
                              | attrMaskable               -> ["/" <> mkMask attrFormat m]
                              | otherwise                  -> error $ "OVS.mkMatch: wildcards not allowed for field " ++ show matchField

mkExprA :: OF.Expr -> Doc
mkExprA (OF.EVal v)       = pp $ OF.valVal v
mkExprA (OF.EField f msl) = pp f' <> sl'
    where 
    (f', msl') = case M.lookup (OF.fieldName f) assnMap of
                      Nothing              -> error $ "OVS.mkExprA: unknown field " ++ OF.fieldName f
                      Just (n, Nothing)    -> (n, msl)
                      Just (n, Just (h,l)) -> (n, maybe (Just (h,l)) (\(h',l') -> Just (l+h',l+l')) msl)
    sl' = case msl' of
               Nothing    -> "[]"
               Just (h,l) -> "[" <> pp l <> ".." <> pp h <> "]"

mkAction :: OF.Action -> Doc
mkAction (OF.ActionOutput p)          = "output:" <> mkExprA p
mkAction (OF.ActionGroup  g)          = "group:" <> pp g
mkAction OF.ActionDrop                = "drop"
mkAction (OF.ActionSet l r@OF.EVal{}) = "load:" <> mkExprA r <> "->" <> mkExprA l
mkAction (OF.ActionSet l r)           = "move:" <> mkExprA r <> "->" <> mkExprA l
mkAction (OF.ActionGoto t)            = "goto_table:" <> pp t
mkAction OF.ActionController          = "controller"
    --"controller(userdata=" <> (hcat $ punctuate "." $ map (pp . (\w -> (printf "%02x" w) :: String)) u) <> ")"

mkBucket :: OF.Bucket -> Doc
mkBucket (OF.Bucket mid as) = commaCat [ maybe empty (("bucket=" <>) . pp) mid
                                       , "actions=" <> (commaCat $ map mkAction as)]

pprintf x y = text $ printf x y

mkVal :: Format -> Integer -> Doc
mkVal Hex v = "0x" <> (pp $ showHex v "")
mkVal Dec v = pp v
mkVal IP4 v = (pp $ bitSlice v 31 24) <> "." <> (pp $ bitSlice v 23 16) <> "." <> (pp $ bitSlice v 15 8) <> "." <> (pp $ bitSlice v 7 0)
mkVal IP6 v = (pprintf "%04x" $ bitSlice v 127 112) <> ":" <> (pprintf "%04x" $ bitSlice v 111 96) <> ":" <> 
              (pprintf "%04x" $ bitSlice v 95 80) <> ":" <> (pprintf "%04x" $ bitSlice v 79 64) <> ":" <>
              (pprintf "%04x" $ bitSlice v 63 48) <> ":" <> (pprintf "%04x" $ bitSlice v 47 32) <> ":" <> 
              (pprintf "%04x" $ bitSlice v 31 16) <> ":" <> (pprintf "%04x" $ bitSlice v 15 0)
mkVal MAC v = (pprintf "%02x" $ bitSlice v 47 40) <> ":" <> (pprintf "%02x" $ bitSlice v 39 32) <> ":" <> (pprintf "%02x" $ bitSlice v 31 24) <> ":" <> 
              (pprintf "%02x" $ bitSlice v 23 16) <> ":" <> (pprintf "%02x" $ bitSlice v 15 8) <> ":" <> (pprintf "%02x" $ bitSlice v 7 0)

mkMask :: Format -> OF.Mask -> Doc
mkMask f m = mkVal f m
