{-# LANGUAGE QuasiQuotes #-}

module P4.Header ( p4HeaderDecls
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
|        bit<16> tag;
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
|
|parser start {
|    return parse_ethernet;
|}
|
|#define ETHERTYPE_VLAN 0x8100, 0x9100, 0x9200, 0x9300
|#define ETHERTYPE_IPV4 0x0800
|#define ETHERTYPE_ARP  0x0806
|
|
|parser parse_vlan {
|    extract(vlan);
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
|]

p4DefaultDecls::String
p4DefaultDecls = [str|
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
                      _      -> error $ "P4.Header.p4InitHeader: unknown header " ++ h

p4CleanupHeader :: String -> String
p4CleanupHeader h = case h of
                         "vlan" -> "modify_field(eth.etherType, ETHERTYPE_IPV4);"
                         "arp"  -> ""
                         _      -> error $ "P4.Header.p4InitHeader: unknown header " ++ h
