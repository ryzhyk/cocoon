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

-- Parse binary packet header

{-# LANGUAGE RecordWildCards #-}

module OpenFlow.OVSPacket(packet2Expr) where

import qualified Data.Map as M

import Network.Data.Ethernet
import Network.Data.IPv4

import OpenFlow.OVSConst
import Network.Data.OF13.Message 

import Syntax

packet2Expr :: M.Map OXKey OXM -> EthernetFrame -> Expr
packet2Expr oxmmap (h, b) = 
    eStruct "EthPacket" 
            [ eStruct "VXLAN" [tun_dst, tun_id]
            , eBit 16 portnum
            , eBit 48 $ fromIntegral $ etherSrc h
            , eBit 48 $ fromIntegral $ etherDst h
            , vlan 
            , case b of
                   IPInEthernet      ip                 -> eStruct "EthIP4" [ip4Pkt2Expr ip]
                   ARPInEthernet     arp                -> eStruct "EthARP" [arpPkt2Expr arp]
                   LLDPInEthernet    _                  -> eStruct "EthOther" [eBit 16 0x88CC]
                   MagellanP4Packet  _                  -> eStruct "EthOther" [eBit 16 0x9999]
                   OtherEthernetBody (UnknownFrame c _) -> eStruct "EthOther" [eBit 16 $ toInteger c]
            ]
    where
    tun_id = case M.lookup OTunnelID oxmmap of
                  Just (OXM (TunnelID i _) _) -> eBit 64 $ toInteger i
                  _                           -> eBit 64 0

    tun_dst = eBit 32 0 -- OVS does not seem to send tun_dst value to the controller 
    portnum = case M.lookup OInPort oxmmap of
                   Just (InPort pnum) -> toInteger pnum
                   _                  -> 0
    vlan = case h of 
                EthernetHeader{}  -> eStruct "VLAN" [eBit 3 0, eBit 12 0]
                Ethernet8021Q{..} -> eStruct "VLAN" [eBit 3 (toInteger priorityCodePoint), eBit 12 (toInteger vlanId)]
    
ip4Pkt2Expr :: IPPacket -> Expr
ip4Pkt2Expr (IPHeader{..}, b) = 
    eStruct "IP4Pkt" [ eBit 6 $ toInteger dscp
                     , eBit 2 $ toInteger ecn
                     , eBit 8 $ toInteger ttl
                     , eBit 8 $ toInteger nwproto
                     , eBit 32 $ toInteger ipSrcAddress
                     , eBit 32 $ toInteger ipDstAddress
                     , case b of
                            UDPInIP sport dport   -> eStruct "UDPPkt" [eBit 16 $ toInteger sport, eBit 16 $ toInteger dport]
                            ICMPInIP (t,c) _ _    -> eStruct "ICMP4Pkt" [eBit 8 $ toInteger t, eBit 8 $ toInteger c]
                            _                     -> eStruct "IPOther" [eBit 8 $ toInteger nwproto]
                     ]

arpPkt2Expr :: ARPPacket -> Expr
arpPkt2Expr (ARPQuery ARPQueryPacket{..}) = 
    eStruct "ARPPacket" [ eStruct "ARPRequest" []
                        , eBit 32 $ toInteger querySenderIPAddress
                        , eBit 32 $ toInteger queryTargetIPAddress
                        , eBit 48 $ toInteger querySenderEthernetAddress
                        , eBit 48 $ toInteger queryTargetEthernetAddress]
arpPkt2Expr (ARPReply ARPReplyPacket{..}) =
    eStruct "ARPPacket" [ eStruct "ARPReply" []
                        , eBit 32 $ toInteger replySenderIPAddress
                        , eBit 32 $ toInteger replyTargetIPAddress
                        , eBit 48 $ toInteger replySenderEthernetAddress
                        , eBit 48 $ toInteger replyTargetEthernetAddress]


{-

typedef arp_op_t = ARPRequest 
                 | ARPReply
                 //| ARPOther {opcode : bit<16>}

typedef arp_pkt_t = ARPPkt { op  : arp_op_t
                           , spa : ip4_addr_t
                           , tpa : ip4_addr_t
                           , sha : mac_addr_t
                           , tha : mac_addr_t}

typedef ip_payload_t = IPTCP   { tcp : tcp_pkt_t}
                     | IPUDP   { udp : udp_pkt_t}
                     | IPICMP4 { icmp4 : icmp4_pkt_t}
                     | IPICMP6 { icmp6 : icmp6_pkt_t}
                     //| IPOther { protocol : bit<8>}

typedef tcp_pkt_t = TCPPkt { src   : bit<16>
                           , dst   : bit<16>
                           , flags : bit<9> }

typedef udp_pkt_t = UDPPkt { src   : bit<16>
                           , dst   : bit<16> }

typedef icmp4_pkt_t = ICMP4Pkt { type : bit<8>
                               , code : bit<8> }

typedef icmp6_pkt_t = ICMP6Pkt { type : bit<8>
                               , code : bit<8> } -}
