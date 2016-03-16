{-# LANGUAGE QuasiQuotes #-}

module P4.Header (p4HeaderDecls) where

import Text.Heredoc

p4HeaderDecls :: String
p4HeaderDecls = [str|
|header_type ethernet_t {
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
|parser start {
|    return parse_ethernet;
|}
|
|#define ETHERTYPE_VLAN 0x8100, 0x9100, 0x9200, 0x9300
|#define ETHERTYPE_IPV4 0x0800
|
|header ethernet_t ethernet;
|
|parser parse_vlan {
|    extract(vlan_tag);
|    return select(latest.etherType) {
|        ETHERTYPE_IPV4 : parse_ipv4;
|    }
|}
|
|parser parse_ethernet {
|    extract(ethernet);
|    return select(latest.etherType) {
|        ETHERTYPE_VLAN : parse_vlan;
|        ETHERTYPE_IPV4 : parse_ipv4;
|    }
|}
|
|header ipv4_t ip4;
|
|parser parse_ipv4 {
|    extract(ip4);
|    return ingress;
|}
|action yes(){}
|action no(){}
|]
