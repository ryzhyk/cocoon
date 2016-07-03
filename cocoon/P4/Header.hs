{-
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

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
{-# LANGUAGE QuasiQuotes #-}

module P4.Header ( p4HeaderDecls
                 , p4DefaultCommands
                 , p4DefaultDecls
                 , p4InitHeader
                 , p4CleanupHeader) where

import Text.Heredoc

p4HeaderDecls :: String
p4HeaderDecls = [str|
|header_type intrinsic_metadata_t {
|    fields {
|        bit<4> mgid;
|    }
|}
|
|header_type eth_t {
|    fields {
|        bit<48> dstAddr;
|        bit<48> srcAddr;
|        bit<16> etherType;
|    }
|}
|
|header_type vlan_tag_t {
|    fields {
|        bit<16> vid;
|        bit<16> etherType;
|    }
|}
|
|header_type mtag_t {
|    fields {
|        bit<8>  up1;
|        bit<8>  up2;
|        bit<8>  down1;
|        bit<8>  down2;
|        bit<16> etherType;
|    }
|}
|
|header_type stag_t {
|    fields {
|        bit<8>  srcColor;
|        bit<16> etherType;
|    }
|}
|
|header_type ipv4_t {
|    fields {
|        bit<4>  version;
|        bit<4>  ihl;
|        bit<8>  diffserv;
|        bit<16> totalLen;
|        bit<16> identification;
|        bit<3>  flags;
|        bit<13> fragOffset;
|        bit<8>  ttl;
|        bit<8>  protocol;
|        bit<16> hdrChecksum;
|        bit<8>  src_ip3;
|        bit<8>  src_ip2;
|        bit<8>  src_ip1;
|        bit<8>  src_ip0;
|        bit<8>  dst_ip3;
|        bit<8>  dst_ip2;
|        bit<8>  dst_ip1;
|        bit<8>  dst_ip0;
|    }
|}
|
|header_type arp_t {
|    fields {
|        bit<16> htype;
|        bit<16> ptype;
|        bit<8>  hlen;
|        bit<8>  plen;
|        bit<16> oper;
|        bit<48> sha;
|        bit<32> spa;
|        bit<48> tha;
|        bit<32> tpa;
|    }
|}
|   
|metadata intrinsic_metadata_t intrinsic_metadata;
|header eth_t eth;
|metadata eth_t _tmp_eth_t;
|header vlan_tag_t vlan;
|metadata vlan_tag_t _tmp_vlan_tag_t;
|header ipv4_t ip4;
|metadata ipv4_t _tmp_ipv4_t;
|header arp_t arp;
|metadata arp_t _tmp_arp_t;
|header mtag_t mtag;
|metadata mtag_t _tmp_mtag_t;
|header stag_t stag;
|metadata stag_t _tmp_stag_t;
|
|parser start {
|    return parse_ethernet;
|}
|
|#define ETHERTYPE_VLAN 0x8100, 0x9100, 0x9200, 0x9300
|#define ETHERTYPE_MTAG 0xaaaa
|#define ETHERTYPE_STAG 0xaaab
|#define ETHERTYPE_IPV4 0x0800
|#define ETHERTYPE_ARP  0x0806
|
|
|parser parse_vlan {
|    extract(vlan);
|    return select(latest.etherType) {
|        ETHERTYPE_IPV4 : parse_ipv4;
|        ETHERTYPE_ARP  : parse_arp;
|        ETHERTYPE_MTAG : parse_mtag;
|    }
|}
|
|parser parse_mtag {
|    extract(mtag);
|    return select(latest.etherType) {
|        ETHERTYPE_IPV4 : parse_ipv4;
|        ETHERTYPE_ARP  : parse_arp;
|        ETHERTYPE_STAG : parse_stag;
|    }
|}
|
|parser parse_stag {
|    extract(stag);
|    return select(latest.etherType) {
|        ETHERTYPE_IPV4 : parse_ipv4;
|        ETHERTYPE_ARP  : parse_arp;
|    }
|}
|
|parser parse_ethernet {
|    extract(eth);
|    return select(latest.etherType) {
|        ETHERTYPE_VLAN : parse_vlan;
|        ETHERTYPE_IPV4 : parse_ipv4;
|        ETHERTYPE_ARP  : parse_arp;
|    }
|}
|parser parse_arp {
|    return select(current(16, 32)) {
|        0x08000604 : parse_arp_ip4;
|    }
|}
|
|parser parse_arp_ip4 {
|    extract(arp);
|    return ingress;
|}
|
|parser parse_ipv4 {
|    extract(ip4);
|    return ingress;
|}
|action yes(){}
|action no(){}
|
|action broadcast() {
|    modify_field(intrinsic_metadata.mgid, 1);
|}
|
|action adrop() {
|    drop();
|}
|
|table drop {
|    actions {adrop;}
|}
|
|]

p4DefaultDecls::String
p4DefaultDecls = [str|
|]


p4DefaultCommands::String
p4DefaultCommands = [str|
|table_set_default drop adrop
|]

p4InitHeader :: String -> String
p4InitHeader h = case h of
                      "vlan" -> "modify_field(eth.etherType, 0x8100);\n" ++
                                "modify_field(vlan.etherType, ETHERTYPE_IPV4);"
                      "arp"  -> "modify_field(eth.etherType, ETHERTYPE_ARP);\n" ++
                                "modify_field(arp.htype, 0x1);\n" ++
                                "modify_field(arp.ptype, 0x0800);\n" ++
                                "modify_field(arp.hlen, 0x6);\n" ++
                                "modify_field(arp.plen, 0x4);"
                      "mtag" -> "modify_field(mtag.etherType, vlan.etherType);\n" ++
                                "modify_field(vlan.etherType, ETHERTYPE_MTAG);\n"
                      "stag" -> "modify_field(stag.etherType, mtag.etherType);\n" ++
                                "modify_field(mtag.etherType, ETHERTYPE_STAG);\n"
                      _      -> error $ "P4.Header.p4InitHeader: unknown header " ++ h

p4CleanupHeader :: String -> String
p4CleanupHeader h = case h of
                         "vlan" -> "modify_field(eth.etherType, ETHERTYPE_IPV4);"
                         "arp"  -> ""
                         "mtag" -> "modify_field(vlan.etherType, mtag.etherType);"
                         "stag" -> "modify_field(mtag.etherType, stag.etherType);"
                         _      -> error $ "P4.Header.p4InitHeader: unknown header " ++ h
