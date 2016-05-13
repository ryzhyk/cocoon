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
|        mgid : 4;
|    }
|}
|
|header_type eth_t {
|    fields {
|        dstAddr : 48;
|        srcAddr : 48;
|        etherType : 16;
|    }
|}
|
|header_type vlan_tag_t {
|    fields {
|        tag : 16;
|        etherType : 16;
|    }
|}
|
|header_type ipv4_t {
|    fields {
|        version : 4;
|        ihl : 4;
|        diffserv : 8;
|        totalLen : 16;
|        identification : 16;
|        flags : 3;
|        fragOffset : 13;
|        ttl : 8;
|        protocol : 8;
|        hdrChecksum : 16;
|        src_ip3 : 8;
|        src_ip2 : 8;
|        src_ip1 : 8;
|        src_ip0 : 8;
|        dst_ip3 : 8;
|        dst_ip2 : 8;
|        dst_ip1 : 8;
|        dst_ip0 : 8;
|    }
|}
|
|header_type arp_t {
|    fields {
|        htype : 16;
|        ptype : 16;
|        hlen  : 8;
|        plen  : 8;
|        oper  : 16;
|        sha   : 48;
|        spa   : 32;
|        tha   : 48;
|        tpa   : 32;
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
