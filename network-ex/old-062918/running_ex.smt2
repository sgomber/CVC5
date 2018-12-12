(set-logic UFDTLIA)
(set-option :fmf-bound true)
(set-option :produce-models true)

(declare-datatype NodeMobile ((R)))
(declare-datatype NodeInfra ((A) (B) (C)))
(declare-datatype NodeBase ((D)))
(declare-datatype Node ((mobile (mnode NodeMobile)) (infra (inode NodeInfra)) (base (bnode NodeBase))))

(declare-datatype RuleMobile ((R1) (R2)))
(declare-datatype RuleInfra ((R3)))

(declare-datatype Channel ((Ch1) (Ch2) (Ch3)))

(declare-datatype CellAssignMobile ((ca (ca_mrule RuleMobile) (ca_mch Channel))))
(declare-datatype CellAssignInfra ((ca (ca_irule RuleInfra) (ca_ich Channel))))
 
; the global policy
(declare-fun policy_mobile (Int NodeMobile) CellAssignMobile)
(declare-fun policy_infra (Int NodeInfra) CellAssignInfra)


;; channel access predicate
; only one node can have access to a channel in a given time
; we map ( Channel, time ) to a single node
(declare-fun channel_access (Channel Int) Node)


;; subprocedures in rules
; argmax
(declare-fun argmax () NodeInfra)
; global base station
(declare-fun global.bs () NodeBase)


; do we choose to send from Node send to Node rcv at given time?
(define-fun is-send ((time Int) (send Node) (rcv Node)) Bool
(or
(and
  (is-mobile send)
  ; send has access to the channel at time
  (= (channel_access (ca_mch (policy_mobile time (mnode send))) time) send)
  ; and transmits to rcv
  (or 
    ; rule R2
    (and
      (= (ca_mrule (policy_mobile time (mnode send))) R2)
      ; rcv must be an infrastructure node, the argmax
      (and (is-infra rcv) (= argmax (inode rcv)))
    )
    ; other rules go here
  )
)
(and
  (is-infra send)
  ; send has access to the channel at time
  (= (channel_access (ca_ich (policy_infra time (inode send))) time) send)
  ; and transmits to rcv
  (or 
    ; rule R3
    (and 
      (= (ca_irule (policy_infra time (inode send))) R3)
      ; rcv must be a base node and the global base station
      (and (is-base rcv) (= global.bs (bnode rcv)))
    )
    ; other rules go here
  )
)
))



; state: for each Node, whether we have transmitted to Node at a given time
(declare-fun trans (Node Int) Bool)

; initial condition: we have transmitted to R
(assert (trans (mobile R) 0))
(assert (not (trans (infra A) 0)))
(assert (not (trans (infra B) 0)))
(assert (not (trans (infra C) 0)))
(assert (not (trans (base D) 0)))


; transition relation
; a node is transmitted to at a given time if 
; (a) it was previous transmitted to, or
; (b) another Node s has been transmitted to, transmits to it at this time
(declare-fun max_period () Int)
(assert (= max_period 2))
(assert (forall ((x Node) (time Int))
(=> (and (< 0 time) (< time max_period))
(= (trans x (+ time 1)) (or (trans x time) (exists ((s Node)) (and (trans s time) (is-send time s x)))))
)
))

; specification: may have transmitted to D by time 2
(assert (trans (base D) 2))

(check-sat)
(get-model)


