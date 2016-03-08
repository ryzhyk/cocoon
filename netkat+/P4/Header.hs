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
|        srcip3 : 8;
|        srcip2 : 8;
|        srcip1 : 8;
|        srcip0 : 8;
|        dstip3 : 8;
|        dstip2 : 8;
|        dstip1 : 8;
|        dstip0 : 8;
|    }
|}
|
|parser start {
|    return parse_ethernet;
|}
|
|#define ETHERTYPE_IPV4 0x0800
|
|header ethernet_t ethernet;
|
|parser parse_ethernet {
|    extract(ethernet);
|    return select(latest.etherType) {
|        ETHERTYPE_IPV4 : parse_ipv4;
|        default: ingress;
|    }
|}
|
|header ipv4_t pkt;
|
|parser parse_ipv4 {
|    extract(pkt);
|    return ingress;
|}
|action yes(){}
|action no(){}
|]
