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

{-# LANGUAGE OverloadedStrings, RecordWildCards, FlexibleContexts #-}

module OpenFlow.OVS (ovsBackend) where

import Text.PrettyPrint
import qualified Data.Map as M
import Text.Printf
import System.FilePath.Posix
import System.Process
import System.Exit
import Control.Monad
import Control.Monad.Except

import Util
import PP
import Backend
import Numeric
import Syntax
import IR.Registers
import qualified OpenFlow.OpenFlow as OF
import qualified OpenFlow.IR2OF    as OF
import qualified IR.IR             as IR
import qualified Datalog.Datalog   as DL
import qualified Datalog           as DL

ovsBackend :: Backend OF.IRSwitches
ovsBackend = Backend { backendStructs      = ovsStructReify
                     , backendValidate     = error "backendValidate not implemented"
                     , backendPrecompile   = ovsPrecompile
                     , backendBuildSwitch  = ovsBuildSwitch
                     , backendUpdateSwitch = ovsUpdateSwitch
                     , backendResetSwitch  = ovsResetSwitch
                     }

ovsPrecompile :: (MonadError String me) => FilePath -> Refine -> me OF.IRSwitches
ovsPrecompile workdir r = OF.precompile ovsStructReify workdir r ovsRegFile

ovsBuildSwitch :: FilePath -> Refine -> DL.Fact -> OF.IRSwitches -> IR.DB -> IO ()
ovsBuildSwitch workdir r f@(DL.Fact rname _) ir db = do
    let swid = DL.factSwitchId r rname f
        E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
        cmds = OF.buildSwitch r (ir M.! rname) db swid
    ovsResetSwitch workdir r f
    sendCmds workdir rname swid swaddr swname cmds

ovsUpdateSwitch :: FilePath -> Refine -> DL.Fact -> OF.IRSwitches -> IR.Delta -> IO ()
ovsUpdateSwitch workdir r f@(DL.Fact rname _) ir delta = do
    let swid = DL.factSwitchId r rname f
        E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
        cmds = OF.updateSwitch r (ir M.! rname) swid delta
    when (not $ null cmds) $ sendCmds workdir rname swid swaddr swname cmds

ovsResetSwitch :: FilePath -> Refine -> DL.Fact -> IO ()
ovsResetSwitch _ r f = do
    let E (EString _ swaddr) = DL.factField r f (\v -> eField v "address")
        E (EString _ swname) = DL.factField r f (\v -> eField v "name")
    reset swaddr swname

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
ovsStructReify = StructReify ovsReifyWidth ovsReifyCons

ovsReifyWidth = M.fromList
                [ ("eth_pkt_t"    , 0)
                , ("vlan_t"       , 16)
                , ("eth_payload_t", 16)
                , ("ip4_pkt_t"    , 0)
                , ("ip6_pkt_t"    , 0)
                , ("arp_op_t"     , 16)
                , ("arp_pkt_t"    , 0)
                , ("ip_payload_t" , 8)
                , ("tcp_pkt_t"    , 0)
                , ("udp_pkt_t"    , 0)
                , ("icmp4_pkt_t"  , 0)
                , ("icmp6_pkt_t"  , 0)
                ] 

ovsReifyCons = M.fromList
               [ ("EthIP4"      , 0x0800)
               , ("EthIP6"      , 0x86dd)
               , ("EthARP"      , 0x0806)
               , ("ARPRequest"  , 0x0001)
               , ("ARPReply"    , 0x0002)
               , ("IPTCP"       , 0x06)
               , ("IPUDP"       , 0x17)
               , ("IPICMP4"     , 0x01)
               , ("IPICMP6"     , 0x3a)
               ]

-- Map IR field names to names known to the backend
type FieldMap = M.Map String (String, Maybe (Int, Int)) 

matchMap :: M.Map String String
matchMap = M.fromList 
           [ ("metadata"                        ,"metadata"   )
           , ("xxreg0"                          ,"xxreg0"     )
           , ("xxreg1"                          ,"xxreg1"     )
           , ("xxreg2"                          ,"xxreg2"     )
           , ("xxreg3"                          ,"xxreg3"     )
           , ("xreg0"                           ,"xreg0"      )
           , ("xreg1"                           ,"xreg1"      )
           , ("xreg2"                           ,"xreg2"      )
           , ("xreg3"                           ,"xreg3"      )
           , ("xreg4"                           ,"xreg4"      )
           , ("xreg5"                           ,"xreg5"      )
           , ("xreg6"                           ,"xreg6"      )
           , ("xreg7"                           ,"xreg7"      )
           , ("reg0"                            ,"reg0"       )
           , ("reg1"                            ,"reg1"       )
           , ("reg2"                            ,"reg2"       )
           , ("reg3"                            ,"reg3"       )
           , ("reg4"                            ,"reg4"       )
           , ("reg5"                            ,"reg5"       )
           , ("reg6"                            ,"reg6"       )
           , ("reg7"                            ,"reg7"       )
           , ("reg8"                            ,"reg8"       )
           , ("reg9"                            ,"reg9"       )
           , ("reg10"                           ,"reg10"      )
           , ("reg11"                           ,"reg11"      )
           , ("reg12"                           ,"reg12"      )
           , ("reg13"                           ,"reg13"      )
           , ("reg14"                           ,"reg14"      )
           , ("reg15"                           ,"reg15"      )
           , ("portnum"                         ,"in_port"    )
           , ("src"                             ,"dl_src"     )
           , ("dst"                             ,"dl_dst"     )
           , ("vlan.pcp"                        ,"dl_vlan_pcp")
           , ("vlan.vid"                        ,"dl_vlan"    )
           , ("payload._tag"                    ,"dl_type"    )
           , ("payload.ip4.dscp"                ,"ip_dscp"    )
           , ("payload.ip4.ecn"                 ,"ip_ecn"     )
           , ("payload.ip4.ttl"                 ,"nw_ttl"     )
           , ("payload.ip4.proto"               ,"ip_proto"   )
           , ("payload.ip4.src"                 ,"nw_src"     )
           , ("payload.ip4.dst"                 ,"nw_dst"     )
           , ("payload.ip6.dscp"                ,"ip_dscp"    )
           , ("payload.ip6.ecn"                 ,"ip_ecn"     )
           , ("payload.ip6.ttl"                 ,"nw_ttl"     )
           , ("payload.ip6.label"               ,"ipv6_label" )
           , ("payload.ip6.proto"               ,"ip_proto"   )
           , ("payload.ip6.src"                 ,"ipv6_src"   )
           , ("payload.ip6.dst"                 ,"ipv6_dst"   )
           , ("payload.arp.op"                  ,"arp_op"     )
           , ("payload.arp.spa"                 ,"arp_spa"    )
           , ("payload.arp.tpa"                 ,"arp_tpa"    )
           , ("payload.arp.sha"                 ,"arp_sha"    )
           , ("payload.arp.tha"                 ,"arp_tha"    )
           , ("payload.ip4.payload._tag"        ,"ip_proto"   )
           , ("payload.ip4.payload.tcp.src"     ,"tcp_src"    )
           , ("payload.ip4.payload.tcp.dst"     ,"tcp_dst"    )
           , ("payload.ip4.payload.tcp.flags"   ,"tcp_flags"  )
           , ("payload.ip4.payload.udp.src"     ,"udp_src"    )
           , ("payload.ip4.payload.udp.dst"     ,"udp_dst"    )
           , ("payload.ip4.payload.icmp4.type"  ,"icmp_type"  )
           , ("payload.ip4.payload.icmp4.code"  ,"icmp_code"  )
           , ("payload.ip4.payload.icmp6.type"  ,"icmp_type"  )
           , ("payload.ip4.payload.icmp6.code"  ,"icmp_code"  )
           , ("payload.ip6.payload._tag"        ,"ip_proto"   )
           , ("payload.ip6.payload.tcp.src"     ,"tcp_src"    )
           , ("payload.ip6.payload.tcp.dst"     ,"tcp_dst"    )
           , ("payload.ip6.payload.tcp.flags"   ,"tcp_flags"  )
           , ("payload.ip6.payload.udp.src"     ,"udp_src"    )
           , ("payload.ip6.payload.udp.dst"     ,"udp_dst"    )
           , ("payload.ip6.payload.icmp4.type"  ,"icmp_type"  )
           , ("payload.ip6.payload.icmp4.code"  ,"icmp_code"  )
           , ("payload.ip6.payload.icmp6.type"  ,"icmp_type"  )
           , ("payload.ip6.payload.icmp6.code"  ,"icmp_code"  )
           ]


assnMap :: FieldMap
assnMap = M.fromList
          [ ("metadata"                        , ("OXM_OF_METADATA"   , Nothing))
          , ("xxreg0"                          , ("NXM_NX_XXREG0"     , Nothing))
          , ("xxreg1"                          , ("NXM_NX_XXREG1"     , Nothing))
          , ("xxreg2"                          , ("NXM_NX_XXREG2"     , Nothing))
          , ("xxreg3"                          , ("NXM_NX_XXREG3"     , Nothing))
          , ("xreg0"                           , ("OXM_OF_PKT_REG0"   , Nothing))
          , ("xreg1"                           , ("OXM_OF_PKT_REG1"   , Nothing))
          , ("xreg2"                           , ("OXM_OF_PKT_REG2"   , Nothing))
          , ("xreg3"                           , ("OXM_OF_PKT_REG3"   , Nothing))
          , ("xreg4"                           , ("OXM_OF_PKT_REG4"   , Nothing))
          , ("xreg5"                           , ("OXM_OF_PKT_REG5"   , Nothing))
          , ("xreg6"                           , ("OXM_OF_PKT_REG6"   , Nothing))
          , ("xreg7"                           , ("OXM_OF_PKT_REG7"   , Nothing))
          , ("reg0"                            , ("NXM_NX_REG0"       , Nothing))
          , ("reg1"                            , ("NXM_NX_REG1"       , Nothing))
          , ("reg2"                            , ("NXM_NX_REG2"       , Nothing))
          , ("reg3"                            , ("NXM_NX_REG3"       , Nothing))
          , ("reg4"                            , ("NXM_NX_REG4"       , Nothing))
          , ("reg5"                            , ("NXM_NX_REG5"       , Nothing))
          , ("reg6"                            , ("NXM_NX_REG6"       , Nothing))
          , ("reg7"                            , ("NXM_NX_REG7"       , Nothing))
          , ("reg8"                            , ("NXM_NX_REG8"       , Nothing))
          , ("reg9"                            , ("NXM_NX_REG9"       , Nothing))
          , ("reg10"                           , ("NXM_NX_REG10"      , Nothing))
          , ("reg11"                           , ("NXM_NX_REG11"      , Nothing))
          , ("reg12"                           , ("NXM_NX_REG12"      , Nothing))
          , ("reg13"                           , ("NXM_NX_REG13"      , Nothing))
          , ("reg14"                           , ("NXM_NX_REG14"      , Nothing))
          , ("reg15"                           , ("NXM_NX_REG15"      , Nothing))
          , ("portnum"                         , ("NXM_OF_IN_PORT"    , Nothing))
          , ("src"                             , ("NXM_OF_ETH_SRC"    , Nothing))
          , ("dst"                             , ("NXM_OF_ETH_DST"    , Nothing))
          , ("vlan.pcp"                        , ("NXM_OF_VLAN_TCI"   , Just (15,13)))
          , ("vlan.vid"                        , ("NXM_OF_VLAN_TCI"   , Just (11,0)))
          , ("payload._tag"                    , ("NXM_OF_ETH_TYPE"   , Nothing))
          , ("payload.ip4.dscp"                , ("NXM_OF_IP_TOS"     , Just (7,2)))
          , ("payload.ip4.ecn"                 , ("NXM_NX_IP_ECN"     , Nothing))
          , ("payload.ip4.ttl"                 , ("NXM_NX_IP_TTL"     , Nothing))
          , ("payload.ip4.proto"               , ("NXM_OF_IP_PROTO"   , Nothing))
          , ("payload.ip4.src"                 , ("NXM_OF_IP_SRC"     , Nothing))
          , ("payload.ip4.dst"                 , ("NXM_OF_IP_DST"     , Nothing))
          , ("payload.ip6.dscp"                , ("NXM_OF_IP_TOS"     , Just (7,2)))
          , ("payload.ip6.ecn"                 , ("NXM_NX_IP_ECN"     , Nothing))
          , ("payload.ip6.ttl"                 , ("NXM_NX_IP_TTL"     , Nothing))
          , ("payload.ip6.label"               , ("NXM_NX_IPV6_LABEL" , Nothing))
          , ("payload.ip6.proto"               , ("NXM_OF_IP_PROTO"   , Nothing))
          , ("payload.ip6.src"                 , ("NXM_NX_IPV6_SRC"   , Nothing))
          , ("payload.ip6.dst"                 , ("NXM_NX_IPV6_DST"   , Nothing))
          , ("payload.arp.op"                  , ("NXM_OF_ARP_OP"     , Nothing))
          , ("payload.arp.spa"                 , ("NXM_OF_ARP_SPA"    , Nothing))
          , ("payload.arp.tpa"                 , ("NXM_OF_ARP_TPA"    , Nothing))
          , ("payload.arp.sha"                 , ("NXM_NX_ARP_SHA"    , Nothing))
          , ("payload.arp.tha"                 , ("NXM_NX_ARP_THA"    , Nothing))
          , ("payload.ip4.payload._tag"        , ("NXM_OF_IP_PROTO"   , Nothing))
          , ("payload.ip4.payload.tcp.src"     , ("NXM_OF_TCP_SRC"    , Nothing))
          , ("payload.ip4.payload.tcp.dst"     , ("NXM_OF_TCP_DST"    , Nothing))
          , ("payload.ip4.payload.udp.src"     , ("NXM_OF_UDP_SRC"    , Nothing))
          , ("payload.ip4.payload.udp.dst"     , ("NXM_OF_UDP_DST"    , Nothing))
          , ("payload.ip4.payload.icmp4.type"  , ("NXM_OF_ICMP_TYPE"  , Nothing))
          , ("payload.ip4.payload.icmp4.code"  , ("NXM_OF_ICMP_CODE"  , Nothing))
          , ("payload.ip4.payload.icmp6.type"  , ("NXM_OF_ICMP_TYPE"  , Nothing))
          , ("payload.ip4.payload.icmp6.code"  , ("NXM_OF_ICMP_CODE"  , Nothing))
          , ("payload.ip6.payload._tag"        , ("NXM_OF_IP_PROTO"   , Nothing))
          , ("payload.ip6.payload.tcp.src"     , ("NXM_OF_TCP_SRC"    , Nothing))
          , ("payload.ip6.payload.tcp.dst"     , ("NXM_OF_TCP_DST"    , Nothing))
          , ("payload.ip6.payload.udp.src"     , ("NXM_OF_UDP_SRC"    , Nothing))
          , ("payload.ip6.payload.udp.dst"     , ("NXM_OF_UDP_DST"    , Nothing))
          , ("payload.ip6.payload.icmp4.type"  , ("NXM_OF_ICMP_TYPE"  , Nothing))
          , ("payload.ip6.payload.icmp4.code"  , ("NXM_OF_ICMP_CODE"  , Nothing))
          , ("payload.ip6.payload.icmp6.type"  , ("NXM_OF_ICMP_TYPE"  , Nothing))
          , ("payload.ip6.payload.icmp6.code"  , ("NXM_OF_ICMP_CODE"  , Nothing))
          ]

matchAttributes :: M.Map String Attributes
matchAttributes = M.fromList
                  [ ("metadata"   , Attributes True  Hex) 
                  , ("reg0"       , Attributes True  Hex)
                  , ("reg1"       , Attributes True  Hex)
                  , ("reg2"       , Attributes True  Hex)
                  , ("reg3"       , Attributes True  Hex)
                  , ("reg4"       , Attributes True  Hex)
                  , ("reg5"       , Attributes True  Hex)
                  , ("reg6"       , Attributes True  Hex)
                  , ("reg7"       , Attributes True  Hex)
                  , ("reg8"       , Attributes True  Hex)
                  , ("reg9"       , Attributes True  Hex)
                  , ("reg10"      , Attributes True  Hex)
                  , ("reg11"      , Attributes True  Hex)
                  , ("reg12"      , Attributes True  Hex)
                  , ("reg13"      , Attributes True  Hex)
                  , ("reg14"      , Attributes True  Hex)
                  , ("reg15"      , Attributes True  Hex)
                  , ("xreg0"      , Attributes True  Hex)
                  , ("xreg1"      , Attributes True  Hex)
                  , ("xreg2"      , Attributes True  Hex)
                  , ("xreg3"      , Attributes True  Hex)
                  , ("xreg4"      , Attributes True  Hex)
                  , ("xreg5"      , Attributes True  Hex)
                  , ("xreg6"      , Attributes True  Hex)
                  , ("xreg7"      , Attributes True  Hex)
                  , ("xxreg0"     , Attributes True  Hex)
                  , ("xxreg1"     , Attributes True  Hex)
                  , ("xxreg2"     , Attributes True  Hex)
                  , ("xxreg3"     , Attributes True  Hex)
                  , ("in_port"    , Attributes False Dec)
                  , ("dl_src"     , Attributes True  MAC)
                  , ("dl_dst"     , Attributes True  MAC)
                  , ("dl_vlan_pcp", Attributes False Dec)
                  , ("dl_vlan"    , Attributes False Hex)
                  , ("dl_type"    , Attributes False Hex)
                  , ("ip_dscp"    , Attributes False Hex)
                  , ("ip_ecn"     , Attributes False Dec)
                  , ("nw_ttl"     , Attributes False Dec)
                  , ("ip_proto"   , Attributes False Dec)
                  , ("nw_src"     , Attributes True  IP4)
                  , ("nw_dst"     , Attributes True  IP4)
                  , ("ipv6_label" , Attributes True  Hex)
                  , ("ipv6_src"   , Attributes True  IP6)
                  , ("ipv6_dst"   , Attributes True  IP6)
                  , ("arp_op"     , Attributes False Dec)
                  , ("arp_spa"    , Attributes True  IP4)
                  , ("arp_tpa"    , Attributes True  IP4)
                  , ("arp_sha"    , Attributes True  MAC)
                  , ("arp_tha"    , Attributes True  MAC)
                  , ("tcp_src"    , Attributes True  Dec)
                  , ("tcp_dst"    , Attributes True  Dec)
                  , ("tcp_flags"  , Attributes True  Hex)
                  , ("udp_src"    , Attributes True  Hex)
                  , ("udp_dst"    , Attributes True  Hex)
                  , ("icmp_type"  , Attributes False Dec)
                  , ("icmp_code"  , Attributes False Dec)
                  ]


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
   (code, stdo, stde) <- readProcessWithExitCode "ovs-ofctl" [swaddr, "del-flowzbundle", swname] ""
   when (code /= ExitSuccess) $ error $ "ovs-ofctl del-flows failed with exit code " ++ show code ++ 
                                        "\noutput: " ++ stdo ++
                                        "\nstd error: " ++ stde
data Format = Hex
            | Dec
            | IP4
            | IP6
            | MAC

data Attributes = Attributes { attrMaskable :: Bool
                             , attrFormat   :: Format
                             }

sendCmds :: FilePath -> String -> Integer -> String -> String -> [OF.Command] -> IO ()
sendCmds workdir swrel swid swaddr swname cmds = do
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
                       Nothing                  -> [empty]
                       Just m | OF.isFullMask m -> [empty]
                              | attrMaskable    -> ["/" <> mkMask attrFormat m]
                              | otherwise       -> error $ "OVS.mkMatch: wildcards not allowed for field " ++ show matchField

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
mkAction (OF.ActionOutput p)          = "output:" <> pp p
mkAction (OF.ActionGroup  g)          = "group:" <> pp g
mkAction OF.ActionDrop                = "drop"
mkAction (OF.ActionSet l r@OF.EVal{}) = "load:" <> mkExprA r <> "->" <> mkExprA l
mkAction (OF.ActionSet l r)           = "move:" <> mkExprA r <> "->" <> mkExprA l
mkAction (OF.ActionGoto t)            = "goto_table:" <> pp t

mkBucket :: OF.Bucket -> Doc
mkBucket (OF.Bucket mid as) = commaCat [ maybe empty (("bucket=" <>) . pp) mid
                                       , "actions=" <> (commaCat $ map mkAction as)]

pprintf x y = text $ printf x y

mkVal :: Format -> OF.Value -> Doc
mkVal Hex (OF.Value _ v) = "0x" <> (pp $ showHex v "")
mkVal Dec (OF.Value _ v) = pp v
mkVal IP4 (OF.Value _ v) = (pp $ bitSlice v 31 24) <> "." <> (pp $ bitSlice v 23 16) <> "." <> (pp $ bitSlice v 15 8) <> "." <> (pp $ bitSlice v 7 0)
mkVal IP6 (OF.Value _ v) = (pprintf "%04x" $ bitSlice v 127 112) <> ":" <> (pprintf "%04x" $ bitSlice v 111 96) <> ":" <> 
                           (pprintf "%04x" $ bitSlice v 95 80) <> ":" <> (pprintf "%04x" $ bitSlice v 79 64) <> ":" <>
                           (pprintf "%04x" $ bitSlice v 63 48) <> ":" <> (pprintf "%04x" $ bitSlice v 47 32) <> ":" <> 
                           (pprintf "%04x" $ bitSlice v 31 16) <> ":" <> (pprintf "%04x" $ bitSlice v 15 0)
mkVal MAC (OF.Value _ v) = (pprintf "%02x" $ bitSlice v 47 40) <> ":" <> (pprintf "%02x" $ bitSlice v 39 32) <> ":" <> (pprintf "%02x" $ bitSlice v 31 24) <> ":" <> 
                           (pprintf "%02x" $ bitSlice v 23 16) <> ":" <> (pprintf "%02x" $ bitSlice v 15 8) <> ":" <> (pprintf "%02x" $ bitSlice v 7 0)

mkMask :: Format -> OF.Mask -> Doc
mkMask f v = mkVal f v
