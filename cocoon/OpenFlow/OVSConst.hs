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

module OpenFlow.OVSConst where

import qualified Data.Map as M
import Data.Word

import IR.Registers
import Backend

data Format = Hex
            | Dec
            | IP4
            | IP6
            | MAC

data Attributes = Attributes { attrMaskable :: Bool
                             , attrFormat   :: Format
                             }

ovsRegFile :: RegisterFile
ovsRegFile = RegisterFile $
             [ {-Register "metadata" 64   [] -} -- reserve metadata register for use in packet-in messages
               Register "xxreg0"   128  [ RegField "xreg0"  64 64
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
           , ("vxlan.tun_dst"                   ,"tun_dst"    )
           , ("vxlan.tun_id"                    ,"tun_id"     )
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
          [ ("metadata"                        , ("OXM_OF_METADATA"    , Nothing))
          , ("xxreg0"                          , ("NXM_NX_XXREG0"      , Nothing))
          , ("xxreg1"                          , ("NXM_NX_XXREG1"      , Nothing))
          , ("xxreg2"                          , ("NXM_NX_XXREG2"      , Nothing))
          , ("xxreg3"                          , ("NXM_NX_XXREG3"      , Nothing))
          , ("xreg0"                           , ("OXM_OF_PKT_REG0"    , Nothing))
          , ("xreg1"                           , ("OXM_OF_PKT_REG1"    , Nothing))
          , ("xreg2"                           , ("OXM_OF_PKT_REG2"    , Nothing))
          , ("xreg3"                           , ("OXM_OF_PKT_REG3"    , Nothing))
          , ("xreg4"                           , ("OXM_OF_PKT_REG4"    , Nothing))
          , ("xreg5"                           , ("OXM_OF_PKT_REG5"    , Nothing))
          , ("xreg6"                           , ("OXM_OF_PKT_REG6"    , Nothing))
          , ("xreg7"                           , ("OXM_OF_PKT_REG7"    , Nothing))
          , ("reg0"                            , ("NXM_NX_REG0"        , Nothing))
          , ("reg1"                            , ("NXM_NX_REG1"        , Nothing))
          , ("reg2"                            , ("NXM_NX_REG2"        , Nothing))
          , ("reg3"                            , ("NXM_NX_REG3"        , Nothing))
          , ("reg4"                            , ("NXM_NX_REG4"        , Nothing))
          , ("reg5"                            , ("NXM_NX_REG5"        , Nothing))
          , ("reg6"                            , ("NXM_NX_REG6"        , Nothing))
          , ("reg7"                            , ("NXM_NX_REG7"        , Nothing))
          , ("reg8"                            , ("NXM_NX_REG8"        , Nothing))
          , ("reg9"                            , ("NXM_NX_REG9"        , Nothing))
          , ("reg10"                           , ("NXM_NX_REG10"       , Nothing))
          , ("reg11"                           , ("NXM_NX_REG11"       , Nothing))
          , ("reg12"                           , ("NXM_NX_REG12"       , Nothing))
          , ("reg13"                           , ("NXM_NX_REG13"       , Nothing))
          , ("reg14"                           , ("NXM_NX_REG14"       , Nothing))
          , ("reg15"                           , ("NXM_NX_REG15"       , Nothing))
          , ("portnum"                         , ("NXM_OF_IN_PORT"     , Nothing))
          , ("src"                             , ("NXM_OF_ETH_SRC"     , Nothing))
          , ("dst"                             , ("NXM_OF_ETH_DST"     , Nothing))
          , ("vxlan.tun_dst"                   , ("NXM_NX_TUN_IPV4_DST", Nothing))
          , ("vxlan.tun_id"                    , ("NXM_NX_TUN_ID"      , Nothing))
          , ("vlan.pcp"                        , ("NXM_OF_VLAN_TCI"    , Just (15,13)))
          , ("vlan.vid"                        , ("NXM_OF_VLAN_TCI"    , Just (11,0)))
          , ("payload._tag"                    , ("NXM_OF_ETH_TYPE"    , Nothing))
          , ("payload.ip4.dscp"                , ("NXM_OF_IP_TOS"      , Just (7,2)))
          , ("payload.ip4.ecn"                 , ("NXM_NX_IP_ECN"      , Nothing))
          , ("payload.ip4.ttl"                 , ("NXM_NX_IP_TTL"      , Nothing))
          , ("payload.ip4.proto"               , ("NXM_OF_IP_PROTO"    , Nothing))
          , ("payload.ip4.src"                 , ("NXM_OF_IP_SRC"      , Nothing))
          , ("payload.ip4.dst"                 , ("NXM_OF_IP_DST"      , Nothing))
          , ("payload.ip6.dscp"                , ("NXM_OF_IP_TOS"      , Just (7,2)))
          , ("payload.ip6.ecn"                 , ("NXM_NX_IP_ECN"      , Nothing))
          , ("payload.ip6.ttl"                 , ("NXM_NX_IP_TTL"      , Nothing))
          , ("payload.ip6.label"               , ("NXM_NX_IPV6_LABEL"  , Nothing))
          , ("payload.ip6.proto"               , ("NXM_OF_IP_PROTO"    , Nothing))
          , ("payload.ip6.src"                 , ("NXM_NX_IPV6_SRC"    , Nothing))
          , ("payload.ip6.dst"                 , ("NXM_NX_IPV6_DST"    , Nothing))
          , ("payload.arp.op"                  , ("NXM_OF_ARP_OP"      , Nothing))
          , ("payload.arp.spa"                 , ("NXM_OF_ARP_SPA"     , Nothing))
          , ("payload.arp.tpa"                 , ("NXM_OF_ARP_TPA"     , Nothing))
          , ("payload.arp.sha"                 , ("NXM_NX_ARP_SHA"     , Nothing))
          , ("payload.arp.tha"                 , ("NXM_NX_ARP_THA"     , Nothing))
          , ("payload.ip4.payload._tag"        , ("NXM_OF_IP_PROTO"    , Nothing))
          , ("payload.ip4.payload.tcp.src"     , ("NXM_OF_TCP_SRC"     , Nothing))
          , ("payload.ip4.payload.tcp.dst"     , ("NXM_OF_TCP_DST"     , Nothing))
          , ("payload.ip4.payload.udp.src"     , ("NXM_OF_UDP_SRC"     , Nothing))
          , ("payload.ip4.payload.udp.dst"     , ("NXM_OF_UDP_DST"     , Nothing))
          , ("payload.ip4.payload.icmp4.type"  , ("NXM_OF_ICMP_TYPE"   , Nothing))
          , ("payload.ip4.payload.icmp4.code"  , ("NXM_OF_ICMP_CODE"   , Nothing))
          , ("payload.ip4.payload.icmp6.type"  , ("NXM_OF_ICMP_TYPE"   , Nothing))
          , ("payload.ip4.payload.icmp6.code"  , ("NXM_OF_ICMP_CODE"   , Nothing))
          , ("payload.ip6.payload._tag"        , ("NXM_OF_IP_PROTO"    , Nothing))
          , ("payload.ip6.payload.tcp.src"     , ("NXM_OF_TCP_SRC"     , Nothing))
          , ("payload.ip6.payload.tcp.dst"     , ("NXM_OF_TCP_DST"     , Nothing))
          , ("payload.ip6.payload.udp.src"     , ("NXM_OF_UDP_SRC"     , Nothing))
          , ("payload.ip6.payload.udp.dst"     , ("NXM_OF_UDP_DST"     , Nothing))
          , ("payload.ip6.payload.icmp4.type"  , ("NXM_OF_ICMP_TYPE"   , Nothing))
          , ("payload.ip6.payload.icmp4.code"  , ("NXM_OF_ICMP_CODE"   , Nothing))
          , ("payload.ip6.payload.icmp6.type"  , ("NXM_OF_ICMP_TYPE"   , Nothing))
          , ("payload.ip6.payload.icmp6.code"  , ("NXM_OF_ICMP_CODE"   , Nothing))
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
                  , ("tun_id"     , Attributes True  Dec)
                  , ("tun_dst"    , Attributes True  IP4)
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


data OXKey = OInPort
           | OInPhyPort
           | OMetadata
           | OEthDst
           | OEthSrc
           | OEthType
           | OIPv4Dst
           | OIPv4Src
           | ONiciraRegister Int
           | OVLANID
           | OVLANPCP
           | OIPDSCP
           | OIPECN
           | OIPProto
           | OTCPSrc
           | OTCPDst
           | OUDPSrc
           | OUDPDst
           | OSCTPSrc
           | OSCTPDst
           | OICMPv4_Type
           | OICMPv4_Code
           | OARP_OP
           | OARP_SPA
           | OARP_TPA
           | OARP_SHA
           | OARP_THA
           | OIPv6Src
           | OIPv6Dst
           | OIPv6_FLabel
           | OICMPv6_Type
           | OICMPv6_Code
           | OIPv6_ND_Target
           | OIPv6_ND_SLL
           | OIPv6_ND_TLL
           | OMPLS_Label
           | OMPLS_TC
           | OMPLS_BOS
           | OPBB_ISID
           | OTunnelID
           | OIPv6_EXTHDR
           | OOXMOther Word16 Word8
           deriving (Eq, Ord)
