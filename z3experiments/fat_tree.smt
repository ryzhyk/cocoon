; Packet: DST IP
(declare-datatypes () ( (IP (ip (ip1 Int) (ip2 Int) (ip3 Int) (ip4 Int))) ) )
(declare-datatypes () ( (Packet (pkt (dst IP))) ) )

; Location: node[IP]
(declare-datatypes () ( (Location0 (node0 (addr0 IP) )
                                   (consumed0 (finaladdr0 IP))
                        )
                      ))

(define-fun k () Int 10)

(declare-var pip1   Int)
(declare-var pip2   Int)
(declare-var pip3   Int)
(declare-var anyint Int)
(declare-var pID    Int)
(declare-var cID    Int)
(declare-var outpID Int)
(declare-var paddr  IP)
(declare-var laddr  IP)
(declare-var naddr  IP)
(declare-var p      Packet)
(declare-var ploc0  Location0)
(declare-var nloc0  Location0)
(declare-var nnloc0 Location0)

(declare-rel trans0   (Packet Location0 Location0))
(declare-rel network0 (Packet Location0 Location0))

(rule (=> (not (= paddr laddr)) (trans0 (pkt paddr) (node0 laddr) (node0 paddr))))
(rule (=> (= paddr laddr) (trans0 (pkt paddr) (node0 laddr) (consumed0 paddr))))

(rule (=> (and (trans0 p ploc0 nloc0) (network0 p nloc0 nnloc0)) (network0 p ploc0 nnloc0) ))
(rule (=> (trans0 p ploc0 (consumed0 naddr)) (network0 p ploc0 (consumed0 naddr))))

(query (and (network0 p ploc0 nloc0) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc0 (node0 (ip 10 10 10 102))) 
                                     (= nloc0 (consumed0 (ip 10 10 10 103))))
;:print-certificate true
)

; Location: node[IP]/fabric

(declare-datatypes () ( (Location1 (node1 (addr1 IP) )
                                   fabric1
                                   (consumed1 (finaladdr1 IP))
                        )
                      ))

(declare-var ploc1  Location1)
(declare-var nloc1  Location1)
(declare-var nnloc1 Location1)

(declare-rel trans1   (Packet Location1 Location1))
(declare-rel network1 (Packet Location1 Location1))

(rule (=> (not (= paddr laddr)) (trans1 (pkt paddr) (node1 laddr) fabric1)))
(rule (=> true (trans1 (pkt paddr) fabric1 (node1 paddr))))
(rule (=> (= paddr laddr) (trans1 (pkt paddr) (node1 laddr) (consumed1 paddr))))

(rule (=> (and (trans1 p ploc1 nloc1) (network1 p nloc1 nnloc1)) (network1 p ploc1 nnloc1) ))
(rule (=> (trans1 p ploc1 (consumed1 naddr)) (network1 p ploc1 (consumed1 naddr))))

(query (and (network1 p ploc1 nloc1) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc1 (node1 (ip 10 10 10 102))) 
                                     (= nloc1 (consumed1 (ip 10 10 10 103))))
;:print-certificate true
)

(declare-rel lift_1_0 (Location1 Location0))
(declare-rel nlift_1_0 (Location1 Location0))

(rule (=> true (lift_1_0 (node1 paddr) (node0 paddr))))
(rule (=> true (lift_1_0 (consumed1 paddr) (consumed0 paddr))))

(rule (=> (not (= ploc0 (node0 paddr))) (nlift_1_0 (node1 paddr) ploc0)))
(rule (=> (not (= ploc0 (consumed0 paddr))) (nlift_1_0 (consumed1 paddr) ploc0)))

(query (and (lift_1_0 ploc1 ploc0) (network0 p ploc0 nloc0) (network1 p ploc1 nloc1) (nlift_1_0 nloc1 nloc0))
:print-certificate true
)

; Location: node[IP]/pod/core

(declare-datatypes () ( (Location2 (node2 (addr2 IP) )
                                   core2
                                   (pod2 (podip1 Int) (podip2 Int))
                                   (consumed2 (finaladdr2 IP))
                        )
                      ))

(declare-var ploc2  Location2)
(declare-var nloc2  Location2)
(declare-var nnloc2 Location2)

(declare-rel trans2   (Packet Location2 Location2))
(declare-rel network2 (Packet Location2 Location2))

(rule (=> (= paddr laddr) (trans2 (pkt paddr) (node2 laddr) (consumed2 paddr))))
(rule (=> (not (= paddr laddr)) (trans2 (pkt paddr) (node2 laddr) (pod2 (ip1 laddr) (ip2 laddr)))))
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2))) 
          (trans2 (pkt paddr) (pod2 pip1 pip2) core2)))
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2)) 
          (trans2 (pkt paddr) (pod2 pip1 pip2) (node2 paddr))))
(rule (=> true (trans2 (pkt paddr) core2 (pod2 (ip1 paddr) (ip2 paddr)))))

(rule (=> (and (trans2 p ploc2 nloc2) (network2 p nloc2 nnloc2)) (network2 p ploc2 nnloc2) ))
(rule (=> (trans2 p ploc2 (consumed2 naddr)) (network2 p ploc2 (consumed2 naddr))))

(query (and (network2 p ploc2 nloc2) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc2 (node2 (ip 10 10 10 102))) 
                                     (= nloc2 (consumed2 (ip 10 10 10 103))))
;:print-certificate true
)

; Location: node[IP]/podupper/podlower/core

(declare-datatypes () ( (Location3 (node3 (addr3 IP) )
                                   core3
                                   (podupper3 (podupip1 Int) (podupip2 Int) )
                                   (podlower3 (podloip1 Int) (podloip2 Int) (podloip3 Int))
                                   (consumed3 (finaladdr3 IP))
                        )
                      ))

(declare-var ploc3  Location3)
(declare-var nloc3  Location3)
(declare-var nnloc3 Location3)

(declare-rel trans3   (Packet Location3 Location3))
(declare-rel network3 (Packet Location3 Location3))

;node
(rule (=> (= paddr laddr) (trans3 (pkt paddr) (node3 laddr) (consumed3 paddr))))
(rule (=> (not (= paddr laddr)) (trans3 (pkt paddr) (node3 laddr) (podlower3 (ip1 laddr) (ip2 laddr) (ip3 laddr)))))

;podupper
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2))) 
          (trans3 (pkt paddr) (podupper3 pip1 pip2) core3)))
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2)) 
          (trans3 (pkt paddr) (podupper3 pip1 pip2) (podlower3 pip1 pip2 (ip3 paddr)))))
;podlower
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2) (= (ip3 paddr) pip3))
          (trans3 (pkt paddr) (podlower3 pip1 pip2 pip3) (node3 paddr))))
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2)) (not (= (ip3 paddr) pip3))) 
          (trans3 (pkt paddr) (podlower3 pip1 pip2 pip3) (podupper3 pip1 pip2))))
;core
(rule (=> true (trans3 (pkt paddr) core3 (podupper3 (ip1 paddr) (ip2 paddr)))))

(rule (=> (and (trans3 p ploc3 nloc3) (network3 p nloc3 nnloc3)) (network3 p ploc3 nnloc3) ))
(rule (=> (trans3 p ploc3 (consumed3 naddr)) (network3 p ploc3 (consumed3 naddr))))


(query (and (network3 p ploc3 nloc3) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc3 (node3 (ip 10 10 10 102))) 
                                     (= nloc3 (consumed3 (ip 10 10 10 101))))
;:print-certificate true
)


; Location: node[IP]/podupper/podlower/core

(declare-datatypes () ( (Location4 (node4 (addr4 IP) )
                                   core4
                                   (podupper4 (podupip1 Int) (podupip2 Int) (podupID Int))
                                   (podlower4 (podloip1 Int) (podloip2 Int) (podloip3 Int))
                                   (consumed4 (finaladdr4 IP))
                        )
                      ))

(declare-var ploc4  Location4)
(declare-var nloc4  Location4)
(declare-var nnloc4 Location4)

(declare-rel trans4   (Packet Location4 Location4))
(declare-rel network4 (Packet Location4 Location4))

;node
(rule (=> (= paddr laddr) (trans4 (pkt paddr) (node4 laddr) (consumed4 paddr))))
(rule (=> (not (= paddr laddr)) (trans4 (pkt paddr) (node4 laddr) (podlower4 (ip1 laddr) (ip2 laddr) (ip3 laddr)))))

;podupper
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2))) 
          (trans4 (pkt paddr) (podupper4 pip1 pip2 anyint) core4)))
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2)) 
          (trans4 (pkt paddr) (podupper4 pip1 pip2 anyint) (podlower4 pip1 pip2 (ip3 paddr)))))
;podlower
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2) (= (ip3 paddr) pip3))
          (trans4 (pkt paddr) (podlower4 pip1 pip2 pip3) (node4 paddr))))
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2)) (not (= (ip3 paddr) pip3))) 
          (trans4 (pkt paddr) (podlower4 pip1 pip2 pip3) (podupper4 pip1 pip2 (mod (+ (ip4 paddr) pip3) (/ k 2))))))
;core
(rule (=> (<= anyint k) (trans4 (pkt paddr) core4 (podupper4 (ip1 paddr) (ip2 paddr) anyint))))

(rule (=> (and (trans4 p ploc4 nloc4) (network4 p nloc4 nnloc4)) (network4 p ploc4 nnloc4) ))
(rule (=> (trans4 p ploc4 (consumed4 naddr)) (network4 p ploc4 (consumed4 naddr))))


(query (and (network4 p ploc4 nloc4) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc4 (node4 (ip 10 9 9 102))) 
                                     (= nloc4 (consumed4 (ip 10 10 10 101))))
;:print-certificate true
)

; Location: node[IP]/podupper/podlower/core

(declare-datatypes () ( (Location5 (node5 (addr5 IP) )
                                   (core5 (coreID Int))
                                   (podupper5 (podupip1 Int) (podupip2 Int) (podupID Int))
                                   (podlower5 (podloip1 Int) (podloip2 Int) (podloip3 Int))
                                   (consumed5 (finaladdr5 IP))
                        )
                      ))

(declare-var ploc5  Location5)
(declare-var nloc5  Location5)
(declare-var nnloc5 Location5)

(declare-rel trans5   (Packet Location5 Location5))
(declare-rel network5 (Packet Location5 Location5))

;node
(rule (=> (= paddr laddr) (trans5 (pkt paddr) (node5 laddr) (consumed5 paddr))))
(rule (=> (not (= paddr laddr)) (trans5 (pkt paddr) (node5 laddr) (podlower5 (ip1 laddr) (ip2 laddr) (ip3 laddr)))))

;podupper
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2))) 
          (trans5 (pkt paddr) (podupper5 pip1 pip2 pID) (core5 (+ (* pID (/ k 2)) (mod (+ (ip4 paddr) pID) (/ k 2)))))))
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2)) 
          (trans5 (pkt paddr) (podupper5 pip1 pip2 anyint) (podlower5 pip1 pip2 (ip3 paddr)))))
;podlower
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2) (= (ip3 paddr) pip3))
          (trans5 (pkt paddr) (podlower5 pip1 pip2 pip3) (node5 paddr))))
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2)) (not (= (ip3 paddr) pip3))) 
          (trans5 (pkt paddr) (podlower5 pip1 pip2 pip3) (podupper5 pip1 pip2 (mod (+ (ip4 paddr) pip3) (/ k 2))))))
;core
(rule (=> true (trans5 (pkt paddr) (core5 cID) (podupper5 (ip1 paddr) (ip2 paddr) (/ cID 2)))))

(rule (=> (and (trans5 p ploc5 nloc5) (network5 p nloc5 nnloc5)) (network5 p ploc5 nnloc5) ))
(rule (=> (trans5 p ploc5 (consumed5 naddr)) (network5 p ploc5 (consumed5 naddr))))


(query (and (network5 p ploc5 nloc5) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc5 (node5 (ip 10 9 9 102))) 
                                     (= nloc5 (consumed5 (ip 10 10 10 101))))
;:print-certificate true
)


; Location: node[IP]/podupper/podlower/core

(declare-datatypes () ( (Location6 (node6 (addr6 IP) )
                                   (corein6 (coreinID Int) (coreinp Int))
                                   (coreout6 (coreoutID Int) (coreoutp Int))
                                   (podupper6 (podupip1 Int) (podupip2 Int) (podupID Int))
                                   (podlower6 (podloip1 Int) (podloip2 Int) (podloip3 Int))
                                   (consumed6 (finaladdr5 IP))
                        )
                      ))

(declare-var ploc6  Location6)
(declare-var nloc6  Location6)
(declare-var nnloc6 Location6)

(declare-rel trans6   (Packet Location6 Location6))
(declare-rel network6 (Packet Location6 Location6))

;node
(rule (=> (= paddr laddr) (trans6 (pkt paddr) (node6 laddr) (consumed6 paddr))))
(rule (=> (not (= paddr laddr)) (trans6 (pkt paddr) (node6 laddr) (podlower6 (ip1 laddr) (ip2 laddr) (ip3 laddr)))))

;podupper
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2)))
          (trans6 (pkt paddr) (podupper6 pip1 pip2 pID) (corein6 (+ (* pID (/ k 2)) (mod (+ (ip4 paddr) pID) (/ k 2))) pip2 ))))
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2)) 
          (trans6 (pkt paddr) (podupper6 pip1 pip2 anyint) (podlower6 pip1 pip2 (ip3 paddr)))))
;podlower
(rule (=> (and (= (ip1 paddr) pip1) (= (ip2 paddr) pip2) (= (ip3 paddr) pip3))
          (trans6 (pkt paddr) (podlower6 pip1 pip2 pip3) (node6 paddr))))
(rule (=> (or (not (= (ip1 paddr) pip1)) (not (= (ip2 paddr) pip2)) (not (= (ip3 paddr) pip3))) 
          (trans6 (pkt paddr) (podlower6 pip1 pip2 pip3) (podupper6 pip1 pip2 (mod (+ (ip4 paddr) pip3) (/ k 2))))))
;core
(rule (=> true (trans6 (pkt paddr) (corein6 cID anyint) (coreout6 cID (ip2 paddr)))))
(rule (=> true (trans6 (pkt paddr) (coreout6 cID outpID) (podupper6 (ip1 paddr) outpID (/ cID (/ k 2) )))))

(rule (=> (and (trans6 p ploc6 nloc6) (network6 p nloc6 nnloc6)) (network6 p ploc6 nnloc6) ))
(rule (=> (trans6 p ploc6 (consumed6 naddr)) (network6 p ploc6 (consumed6 naddr))))

(query (and (network6 p ploc6 nloc6) (= p (pkt (ip 10 10 10 101))) 
                                     (= ploc6 (node6 (ip 10 9 9 102))) 
                                     (= nloc6 (consumed6 (ip 10 10 10 101))))
;:print-certificate true
)

