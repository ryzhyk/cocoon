(declare-datatypes () ( (IP (ip (ip1 Int) (ip2 Int) (ip3 Int) (ip4 Int))) ) )
(declare-datatypes () ( (Packet (pkt (src IP) (srcport Int) (dst IP) (dstPort Int))) ) ) ; skip protocol to keep things simpler
(declare-datatypes () ( (FlowID (flow (src IP) (srcport Int) (dst IP) (dstPort Int))) ) ) 


(define-fun youtubeIP () IP (ip 74 125 239 110))

; extract flow id from packet
(define-fun pktflow ((p Packet)) FlowID 
 (flow (src p) (srcport p) (dst p) (dstPort p))
)


(declare-var ppkt  Packet)
(declare-var npkt  Packet)
(declare-var nnpkt Packet)
(declare-var idsip IP)
(declare-var naddr IP)
(declare-var xflow FlowID)
(declare-var i     Int)
(declare-var j     Int)
(declare-var xp    Int)
(declare-var xl    Int)
(declare-var xxl   Int)

; Location0: ingress/IDS[nodeIP]/transcoder[flow]/node[IP]

(declare-datatypes () ( (Location0 ingress0
                                   (ids0 (idsnodeip IP))
                                   (transcoder0 (xflowid FlowID))
                                   (node0 (addr IP))
                                   dropped0
                                   (consumed0 (finaladdr IP))
                        )
                      ))


(declare-var ploc0 Location0)
(declare-var nloc0 Location0)
(declare-var nnloc0 Location0)

(declare-rel trans0   (Packet Location0 Packet Location0))
(declare-rel network0 (Packet Location0 Packet Location0))

;ingress
(rule (=> (= (src ppkt) youtubeIP) (trans0 ppkt ingress0 ppkt (ids0 (dst ppkt)) )))
(rule (=> (not (= (src ppkt) youtubeIP)) (trans0 ppkt ingress0 ppkt dropped0)))

;ids
(rule (=> (= (dst ppkt) idsip) (trans0 ppkt (ids0 idsip) ppkt (transcoder0 (pktflow ppkt)) )))

;transcoder
(rule (=> (= (pktflow ppkt) xflow) (trans0 ppkt (transcoder0 xflow) ppkt (node0 (dst ppkt)) )))

;node
(rule (=> (= (dst ppkt) naddr) (trans0 ppkt (node0 naddr) ppkt (consumed0 naddr) )))

; network
(rule (=> (and (trans0 ppkt ploc0 npkt nloc0) (network0 npkt nloc0 nnpkt nnloc0)) (network0 ppkt ploc0 nnpkt nnloc0) ))
(rule (=> (trans0 ppkt ploc0 npkt (consumed0 naddr)) (network0 ppkt ploc0 npkt (consumed0 naddr))))
(rule (=> (trans0 ppkt ploc0 npkt dropped0) (network0 ppkt ploc0 npkt dropped0)))

(declare-rel q0 ())
(rule (=> (and (network0 ppkt ploc0 npkt nloc0) (= ppkt (pkt (ip 74 125 239 110) 80 (ip 10 10 10 101) 2000)) 
                                                (= ploc0 ingress0) 
                                                (= nloc0 (consumed0 (ip 10 10 10 101)))) q0)) 

;(query q0
;:print-certificate true
;)


; Location1: ingress/IDS[nodeIP]/transcoder[flow]/BS[BSID]/node[IP]

(declare-datatypes () ( (Location1 ingress1
                                   (ids1 (idsnodeip IP))
                                   (transcoder1 (xflowid FlowID))
                                   (bs1 (bsid Int))
                                   (node1 (addr IP))
                                   dropped1
                                   (consumed1 (finaladdr IP))
                        )
                      ))

(declare-datatypes () ( (Configuration1 (config1 (cfgbs Int))) ) )

(declare-var ploc1     Location1)
(declare-var nloc1     Location1)
(declare-var nnloc1    Location1)
(declare-var pconfig1  Configuration1)
(declare-var nconfig1  Configuration1)
(declare-var nnconfig1 Configuration1)
(declare-var bsid1     Int)

(declare-rel trans1    (Configuration1 Packet Location1 Packet Location1))
(declare-rel reconfig1 (Configuration1 Configuration1))
(declare-rel network1  (Configuration1 Packet Location1 Configuration1 Packet Location1))

;reconfig
(rule (=> true (reconfig1 (config1 i) (config1 j))))

;ingress
(rule (=> (= (src ppkt) youtubeIP) (trans1 pconfig1 ppkt ingress1 ppkt (ids1 (dst ppkt)) )))
(rule (=> (not (= (src ppkt) youtubeIP)) (trans1 pconfig1 ppkt ingress1 ppkt dropped1)))

;ids
(rule (=> (= (dst ppkt) idsip) (trans1 pconfig1 ppkt (ids1 idsip) ppkt (transcoder1 (pktflow ppkt)) )))

;transcoder
(rule (=> (= (pktflow ppkt) xflow) (trans1 pconfig1 ppkt (transcoder1 xflow) ppkt (bs1 (cfgbs pconfig1)) )
      ) 
)

;base station
(rule (=> (= bsid1 (cfgbs pconfig1)) (trans1 pconfig1 ppkt (bs1 bsid1) ppkt (node1 (dst ppkt))) ))
(rule (=> (not (= bsid1 (cfgbs pconfig1))) (trans1 pconfig1 ppkt (bs1 bsid1) ppkt (bs1 (cfgbs pconfig1))) ))

;node
(rule (=> (= (dst ppkt) naddr) (trans1 pconfig1 ppkt (node1 naddr) ppkt (consumed1 naddr) )))

; network
(rule (=> (and (trans1 pconfig1 ppkt ploc1 npkt nloc1) (network1 pconfig1 npkt nloc1 nnconfig1 nnpkt nnloc1)) (network1 pconfig1 ppkt ploc1 nnconfig1 nnpkt nnloc1) ))
(rule (=> (and (reconfig1 pconfig1 nconfig1) (network1 nconfig1 ppkt ploc1 nnconfig1 nnpkt nnloc1)) (network1 pconfig1 ppkt ploc1 nnconfig1 nnpkt nnloc1) ))
(rule (=> (trans1 pconfig1 ppkt ploc1 npkt (consumed1 naddr)) (network1 pconfig1 ppkt ploc1 pconfig1 npkt (consumed1 naddr))))
(rule (=> (trans1 pconfig1 ppkt ploc1 npkt dropped1) (network1 pconfig1 ppkt ploc1 pconfig1 npkt dropped1)))

(declare-rel q1 ())
(rule (=> (and (network1 pconfig1 ppkt ploc1 nconfig1 npkt nloc1) (= pconfig1 (config1 1))
                                                               (= nconfig1 (config1 2))
                                                               (= ppkt (pkt (ip 74 125 239 110) 80 (ip 10 10 10 101) 2000)) 
                                                               (= ploc1 ingress1) 
                                                               (= nloc1 (consumed1 (ip 10 10 10 101)))
                                                        ) q1)) 

;(query q1
;:print-certificate true
;)

; Location2: ingress/IDS[nodeIP]/transcoderNode[hash]/transcoder[flow]/BS[BSID]/node[IP]

(declare-datatypes () ( (Location2 ingress2
                                   (ids2 (idsnodeip IP))
                                   (transcoderNode2 (xnodeid Int))
                                   (transcoder2 (xflowid FlowID))
                                   (bs2 (bsid Int))
                                   (node2 (addr IP))
                                   dropped2
                                   (consumed2 (finaladdr IP))
                        )
                      ))

(declare-datatypes () ( (Configuration2 (config2 (cfgbs Int) 
                                                 (cfgXPartition Int)       ; which transcoder partition the flow belongs to
                                                 (cfgXLocation Int))) ) )  ; where the transcoder for the flow is actually located

(declare-var ploc2     Location2)
(declare-var nloc2     Location2)
(declare-var nnloc2    Location2)
(declare-var pconfig2  Configuration2)
(declare-var nconfig2  Configuration2)
(declare-var nnconfig2 Configuration2)
(declare-var bsid2     Int)

(declare-rel trans2    (Configuration2 Packet Location2 Packet Location2))
(declare-rel reconfig2 (Configuration2 Configuration2))
(declare-rel network2  (Configuration2 Packet Location2 Configuration2 Packet Location2))

;reconfig
(rule (=> true (reconfig2 (config2 i xp xl) (config2 j xp xl))))
(rule (=> (= xp xl) (reconfig2 (config2 i xp xl) (config2 i xp xxl))))
(rule (=> (not (= xp xl)) (reconfig2 (config2 i xp xl) (config2 i xl xl))))

;ingress
(rule (=> (= (src ppkt) youtubeIP) (trans2 pconfig2 ppkt ingress2 ppkt (ids2 (dst ppkt)) )))
(rule (=> (not (= (src ppkt) youtubeIP)) (trans2 pconfig2 ppkt ingress2 ppkt dropped2)))

;ids
(rule (=> (= (dst ppkt) idsip) (trans2 pconfig2 ppkt (ids2 idsip) ppkt (transcoderNode2 (cfgXPartition pconfig2)) )))

;transcoderNode
(rule (=> (= xp (cfgXLocation pconfig2)) (trans2 pconfig2 ppkt (transcoderNode2 xp) ppkt (transcoder2 (pktflow ppkt)) )))
(rule (=> (not (= xp (cfgXLocation pconfig2))) (trans2 pconfig2 ppkt (transcoderNode2 xp) ppkt (transcoderNode2 (cfgXLocation pconfig2)) )))

;transcoder
(rule (=> (= (pktflow ppkt) xflow) (trans2 pconfig2 ppkt (transcoder2 xflow) ppkt (bs2 (cfgbs pconfig2)) )
      ) 
)

;base station
(rule (=> (= bsid2 (cfgbs pconfig2)) (trans2 pconfig2 ppkt (bs2 bsid2) ppkt (node2 (dst ppkt))) ))
(rule (=> (not (= bsid2 (cfgbs pconfig2))) (trans2 pconfig2 ppkt (bs2 bsid2) ppkt (bs2 (cfgbs pconfig2))) ))

;node
(rule (=> (= (dst ppkt) naddr) (trans2 pconfig2 ppkt (node2 naddr) ppkt (consumed2 naddr) )))

; network
(rule (=> (and (trans2 pconfig2 ppkt ploc2 npkt nloc2) (network2 pconfig2 npkt nloc2 nnconfig2 nnpkt nnloc2)) (network2 pconfig2 ppkt ploc2 nnconfig2 nnpkt nnloc2) ))
(rule (=> (and (reconfig2 pconfig2 nconfig2) (network2 nconfig2 ppkt ploc2 nnconfig2 nnpkt nnloc2)) (network2 pconfig2 ppkt ploc2 nnconfig2 nnpkt nnloc2) ))
(rule (=> (trans2 pconfig2 ppkt ploc2 npkt (consumed2 naddr)) (network2 pconfig2 ppkt ploc2 pconfig2 npkt (consumed2 naddr))))
(rule (=> (trans2 pconfig2 ppkt ploc2 npkt dropped2) (network2 pconfig2 ppkt ploc2 pconfig2 npkt dropped2)))

(declare-rel q2 ())
(rule (=> (and (network2 pconfig2 ppkt ploc2 nconfig2 npkt nloc2) (= ppkt (pkt (ip 74 125 239 110) 80 (ip 10 10 10 101) 2000)) 
                                                               (= ploc2 ingress2) 
                                                               (= nloc2 (consumed2 (ip 10 10 10 101)))
                                                        ) q2)) 


(query q2
:print-certificate true
)
