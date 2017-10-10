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

module OpenFlow.OVSPacket( packet2Expr
                         , expr2Packet) where

import qualified Data.Map as M
import qualified Data.ByteString as BS
import Data.Word
import Data.Binary.Put

import Network.Data.Ethernet
import Network.Data.IPv4
import Network.Data.OF13.Message 

import Util
import Syntax
import OpenFlow.OVSConst

packet2Expr :: M.Map OXKey OXM -> EthernetFrame -> (Expr, BS.ByteString)
packet2Expr oxmmap (h, b) = 
    (eStruct "EthPacket" 
             [ eStruct "VXLAN" [tun_dst, tun_id]
             , eBit 16 portnum
             , eBit 48 $ fromIntegral $ etherSrc h
             , eBit 48 $ fromIntegral $ etherDst h
             , vlan 
             , p], pl)
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
    (p, pl) = case b of
                   IPInEthernet      ip                     -> let (ippkt, pload) = ip4Pkt2Expr ip
                                                               in (eStruct "EthIP4" [ippkt], pload)
                   ARPInEthernet     arp                    -> let (arppkt, pload) = arpPkt2Expr arp
                                                               in (eStruct "EthARP" [arppkt], pload)
                   OtherEthernetBody (UnknownFrame c pload) -> (eStruct "EthOther" [eBit 16 $ toInteger c], pload)

    
ip4Pkt2Expr :: IPPacket -> (Expr, BS.ByteString)
ip4Pkt2Expr (IPHeader{..}, b) = 
    (eStruct "IP4Pkt" [ eBit 4  $ toInteger headerLength
                      , eBit 6  $ toInteger dscp
                      , eBit 2  $ toInteger ecn
                      , eBit 16 $ toInteger totalLength
                      , eBit 16 $ toInteger ident
                      , eBit 16 $ toInteger flags
                      , eBit 8  $ toInteger ttl
                      , eBit 8  $ toInteger nwproto
                      , eBit 32 $ toInteger ipSrcAddress
                      , eBit 32 $ toInteger ipDstAddress
                      , p], pl)
    where 
    (p, pl) = case b of
                   UDPInIP udp                 -> udpPkt2Expr udp
                   ICMPInIP icmp               -> icmpPkt2Expr icmp
                   UninterpretedIPBody _ pload -> (eStruct "IPOther" [eBit 8 $ toInteger nwproto], pload)

icmpPkt2Expr :: ICMPPacket -> (Expr, BS.ByteString)
icmpPkt2Expr ((t, c, _), pl) = 
    (eStruct "ICMP4Pkt" [eBit 8 $ toInteger t, eBit 8 $ toInteger c], pl)

arpPkt2Expr :: ARPPacket -> (Expr, BS.ByteString)
arpPkt2Expr (ARPQuery ARPQueryPacket{..}) = 
    (eStruct "ARPPacket" [ eStruct "ARPRequest" []
                         , eBit 32 $ toInteger querySenderIPAddress
                         , eBit 32 $ toInteger queryTargetIPAddress
                         , eBit 48 $ toInteger querySenderEthernetAddress
                         , eBit 48 $ toInteger queryTargetEthernetAddress], BS.empty)
arpPkt2Expr (ARPReply ARPReplyPacket{..}) =
    (eStruct "ARPPacket" [ eStruct "ARPReply" []
                         , eBit 32 $ toInteger replySenderIPAddress
                         , eBit 32 $ toInteger replyTargetIPAddress
                         , eBit 48 $ toInteger replySenderEthernetAddress
                         , eBit 48 $ toInteger replyTargetEthernetAddress], BS.empty)


udpPkt2Expr :: UDPPacket -> (Expr, BS.ByteString)
udpPkt2Expr ((sport, dport, len, _), pl) = 
    (eStruct "UDPPkt" [eBit 16 $ toInteger sport, eBit 16 $ toInteger dport, eBit 16 $ toInteger len] ,pl)

expr2Packet :: Expr -> BS.ByteString -> (EthernetFrame, Word64)
expr2Packet e payload = ((h,b), tunid)
    where
    E (EStruct _ "EthPacket" 
       [ E (EStruct _ "VXLAN" [_,E (EBit _ 64 tun_id)])
       , E (EBit _ 16 _)
       , E (EBit _ 48 src)
       , E (EBit _ 48 dst)
       , vlan
       , pl]) = e
    E (EStruct _"VLAN" 
       [ E (EBit _ 3  pcp)
       , E (EBit _ 12 vid)]) = vlan
    tunid = fromInteger tun_id
    h = case vid of
             0 -> EthernetHeader (fromInteger dst) (fromInteger src)
             _ -> Ethernet8021Q  (fromInteger dst) (fromInteger src) (fromInteger pcp) True (fromInteger vid)
    b = case pl of
             E (EStruct _ "EthIP4" [ip4])               -> IPInEthernet $ expr2IP4Pkt ip4 payload
             E (EStruct _ "EthARP" [arp])               -> ARPInEthernet $ expr2ARPPkt arp
             E (EStruct _ "EthOther" [E (EBit _ _ et)]) -> OtherEthernetBody $ UnknownFrame (fromInteger et) payload
             _                                          -> error $ "OVSPacket.expr2Packet: invalid expression" 
             

expr2ARPPkt :: Expr -> ARPPacket
expr2ARPPkt e = case op of
                     "ARPRequest" -> ARPQuery $ ARPQueryPacket (fromInteger sha) (fromInteger spa) (fromInteger tha) (fromInteger tpa)
                     "ARPReply"   -> ARPReply $ ARPReplyPacket (fromInteger sha) (fromInteger spa) (fromInteger tha) (fromInteger tpa)
                     _            -> error "Unknown ARP operation"
    where
    E (EStruct _ "ARPPacket" [ E (EStruct _ op _)
                             , E (EBit _ 32 sha)
                             , E (EBit _ 32 tha)
                             , E (EBit _ 48 spa)
                             , E (EBit _ 48 tpa)]) = e


expr2IP4Pkt :: Expr -> BS.ByteString -> IPPacket
expr2IP4Pkt e payload = (h,b)
    where
    E (EStruct _ "IP4Pkt" 
       [ E (EBit _ 4  ihl)
       , E (EBit _ 6  dscp)
       , E (EBit _ 2  ecn)
       , E (EBit _ 16 totalLen)
       , E (EBit _ 16 ident)
       , E (EBit _ 16 flagsOff)
       , E (EBit _ 8  ttl)
       , E (EBit _ 8  nwproto)
       , E (EBit _ 32 ipSrcAddress)
       , E (EBit _ 32 ipDstAddress)
       , pl]) = e
    h = IPHeader (fromInteger ipSrcAddress)
                 (fromInteger ipDstAddress)
                 (fromInteger ihl)
                 (fromInteger totalLen)
                 (fromInteger dscp)
                 (fromInteger ecn)
                 (fromInteger ttl)
                 (fromInteger nwproto)
                 csum
                 (fromInteger ident)
                 (fromInteger flagsOff)
    csum = checksum16BS $ runPut $ putIPHeader h 0
    b = case pl of
             E (EStruct _ "UDPPkt" [E (EBit _ 16 sport), E (EBit _ 16 dport), E (EBit _ 16 len)]) 
                                                                        -> UDPInIP ((fromInteger sport, fromInteger dport, fromInteger len, 0), payload)
             E (EStruct _ "ICMP4Pkt" [E (EBit _ 8 t), E (EBit _ 8 c)])  -> let icmp = ((fromInteger t, fromInteger c, cs), payload)
                                                                               cs = checksum16BS $ runPut $ putICMPPacket icmp 0
                                                                           in ICMPInIP icmp
             E (EStruct _ "IPOther" [E (EBit _ 8 proto)])               -> UninterpretedIPBody (fromInteger proto) payload
             _                                                          -> error "OVSPacket expr2IP4Pkt: invalid packet"
