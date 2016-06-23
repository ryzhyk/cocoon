
(declare-sort IPAddress)

(declare-sort Prefix) 
; (declare-datatypes () ((Prefix ((address (_ BitVec 32)) (mask (_ BitVec 32))))))
; or (define-sort Prefix () Int)


(declare-fun prefix-match (IPAddress Prefix) Bool)

; (declare-sort AS)
(define-sort AS () Int)

(define-sort Set (A) (Array A Bool))

(define-sort ASSet () (Set AS))
; (define-sort ASSet () (_ BitVec 48))

; (declare-const bgpdb (Array AS (Set Prefix)))
(declare-fun bgpdb (AS Prefix) Bool)

(define-fun can_route ((as1 AS) (ip IPAddress)) Bool
   (exists ((p Prefix)) (and (prefix-match ip p) (bgpdb as1 p))))


;(define-const bound Int 148)
(declare-const bound Int)

(define-fun-rec bgp_match ((ip IPAddress) (idx Int)) ASSet
     (if (= idx bound) ((as const ASSet) false)
         (store (bgp_match ip (+ idx 1)) idx (can_route idx ip))))


;(declare-fun bgp_match (IPAddress Int) ASSet)
;(assert (forall ((ip IPAddress) (idx Int))
;     (= (bgp_match ip idx) 
;        (if (= idx bound) ((as const ASSet) false)
;         (store (bgp_match ip (+ idx 1)) idx (can_route idx ip))))))


(declare-const ip IPAddress)
(declare-const as0 AS)
(assert (<= 0 as0))
(assert (< as0 bound))

(assert (not (= (select (bgp_match ip 0) as0) (can_route as0 ip))))
(check-sat)
(get-model)

 
   

 