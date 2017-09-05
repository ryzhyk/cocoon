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

{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

module OpenFlow.OVS ( ovsStructReify
                    , ovsSendCmds
                    , ovsReset
                    , ovsFieldMap
                    , ovsRegFile) where

import Text.PrettyPrint
import qualified Data.Map as M
import Text.Printf
import System.Directory
import System.FilePath.Posix
import System.Process
import System.Exit
import Control.Monad

import Util
import PP
import Backend
import Numeric
import OpenFlow.OpenFlow
import IR.Registers

ovsRegFile :: RegisterFile
ovsRegFile = RegisterFile $
             [ Register "metadata" 64   []
             , Register "xxreg0"   128  [ RegField "xreg0"  64 64
                                        , RegField "xreg1"  64 0
                                        , RegField "reg0"   32 96
                                        , RegField "reg1"   32 64
                                        , RegField "reg2"   32 32
                                        , RegField "reg3"   32 0]
             , Register "xxreg1"   128  [ RegField "xreg2"  64 64
                                        , RegField "xreg3"  64 0
                                        , RegField "reg4"   32 96
                                        , RegField "reg5"   32 64
                                        , RegField "reg6"   32 32
                                        , RegField "reg7"   32 0]
             , Register "xxreg2"   128  [ RegField "xreg4"  64 64
                                        , RegField "xreg5"  64 0
                                        , RegField "reg8"   32 96
                                        , RegField "reg9"   32 64
                                        , RegField "reg10"  32 32
                                        , RegField "reg11"  32 0]
             , Register "xxreg3"   128  [ RegField "xreg6"  64 64
                                        , RegField "xreg7"  64 0
                                        , RegField "reg12"  32 96
                                        , RegField "reg13"  32 64
                                        , RegField "reg14"  32 32
                                        , RegField "reg15"  32 0]
             ]


ovsStructReify :: StructReify
ovsStructReify = undefined

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

ovsReset :: String -> String -> IO ()
ovsReset swaddr swname = undefined

data Format = Hex
            | Dec
            | IP4
            | IP6
            | MAC

data Attributes = Attributes { attrMaskable :: Bool
                             , attrFormat   :: Format
                             }

ovsFieldAttributes :: M.Map FName Attributes
ovsFieldAttributes = undefined

ovsFieldMap :: FieldMap
ovsFieldMap = undefined

ovsSendCmds :: FilePath -> String -> Integer -> String -> String -> [Command] -> IO ()
ovsSendCmds workdir swrel swid swaddr swname cmds = do
   let ofcmds = render $ vcat $ map mkCmd cmds
       fname = swrel ++ "-" ++ show swid
       f = workdir </> addExtension fname "of"
   -- write commands to file
   writeFile f ofcmds
   (code, stdo, stde) <- readProcessWithExitCode "ovs-ofctl" [swaddr, "bundle", swname, fname] ""
   when (code /= ExitSuccess) $ error $ "ovs-ofctl failed with exit code " ++ show code ++ 
                                        "\noutput: " ++ stdo ++
                                        "\nstd error: " ++ stde

commaCat = hcat . punctuate comma . filter (not . (==empty))

mkCmd :: Command -> Doc
mkCmd (AddFlow t Flow{..}) = vcat
                             $ map (\m -> "flow add" <+>
                                          commaCat [ "table=" <> pp t
                                                   , "priority=" <> pp flowPriority
                                                   , commaCat m
                                                   , "actions=" <> (commaCat $ map mkAction flowActions)])
                             $ allComb $ map mkMatch flowMatch
mkCmd (DelFlow t p ms)     = vcat 
                             $ map (\m -> "flow delete_strict" <+>
                                          commaCat [ "table=" <> pp t
                                                   , "priority=" <> pp p
                                                   , commaCat m])
                             $ allComb $ map mkMatch ms
mkCmd (AddGroup Group{..}) = "group add" <+>
                              commaCat [ "group_id=" <> pp groupId
                                       , "type=" <> pp groupType
                                       , commaCat $ map (("bucket=" <>) . mkBucket) groupBuckets]
mkCmd (DelGroup gid)       = "group delete" <+> "group_id=" <> pp gid
mkCmd (AddBucket gid b)    = "group insert_bucket" <+> 
                             "group_id=" <> pp gid <> comma <>
                             "bucket=" <> mkBucket b
mkCmd (DelBucket gid bid)  = "group remove_bucket" <+> 
                             "group_id=" <> pp gid <> comma <>
                             "bucket_id=" <> pp bid

mkMatch :: Match -> [Doc]
mkMatch Match{..} = map (\m -> pp matchField <> "=" <> mkVal attrFormat matchVal <> m) masks
    where Field n _ = matchField
          Attributes{..} = ovsFieldAttributes M.! n
          masks = case matchMask of
                       Nothing               -> [empty]
                       Just m | isFullMask m -> [empty]
                              | attrMaskable -> ["/" <> mkMask attrFormat m]
                              | otherwise    -> error $ "OVS.mkMatch: wildcards not allowed for field " ++ show matchField


mkAction :: Action -> Doc
mkAction (ActionOutput p)       = "output:" <> pp p
mkAction (ActionGroup  g)       = "group:" <> pp g
mkAction ActionDrop             = "drop"
mkAction (ActionSet l r@EVal{}) = "load:" <> pp r <> "->" <> pp l
mkAction (ActionSet l r)        = "move:" <> pp r <> "->" <> pp l
mkAction (ActionGoto t)         = "goto_table:" <> pp t

mkBucket :: Bucket -> Doc
mkBucket (Bucket mid as) = commaCat [ maybe empty (("bucket=" <>) . pp) mid
                                    , "actions=" <> (commaCat $ map mkAction as)]

pprintf x y = text $ printf x y

mkVal :: Format -> Value -> Doc
mkVal Hex (Value _ v) = "0x" <> (pp $ showHex v "")
mkVal Dec (Value _ v) = pp v
mkVal IP4 (Value _ v) = (pp $ bitSlice v 31 24) <> "." <> (pp $ bitSlice v 23 16) <> "." <> (pp $ bitSlice v 15 8) <> "." <> (pp $ bitSlice v 7 0)
mkVal IP6 (Value _ v) = (pprintf "%04x" $ bitSlice v 127 112) <> ":" <> (pprintf "%04x" $ bitSlice v 111 96) <> ":" <> 
                        (pprintf "%04x" $ bitSlice v 95 80) <> ":" <> (pprintf "%04x" $ bitSlice v 79 64) <> ":" <>
                        (pprintf "%04x" $ bitSlice v 63 48) <> ":" <> (pprintf "%04x" $ bitSlice v 47 32) <> ":" <> 
                        (pprintf "%04x" $ bitSlice v 31 16) <> ":" <> (pprintf "%04x" $ bitSlice v 15 0)
mkVal MAC (Value _ v) = (pprintf "%02x" $ bitSlice v 47 40) <> ":" <> (pprintf "%02x" $ bitSlice v 39 32) <> ":" <> (pprintf "%02x" $ bitSlice v 31 24) <> ":" <> 
                        (pprintf "%02x" $ bitSlice v 23 16) <> ":" <> (pprintf "%02x" $ bitSlice v 15 8) <> ":" <> (pprintf "%02x" $ bitSlice v 7 0)

mkMask :: Format -> Mask -> Doc
mkMask f v = mkVal f v
