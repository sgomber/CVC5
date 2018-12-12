(set-logic UFDTNIRA)
(set-option :fmf-bound true)
(set-option :produce-models true)

; the probability that either x or y occurs
(define-fun sum_prob ((x Real) (y Real)) Real 
  (+ x (* (- 1.0 x) y))
)
; the probability that both x and y occur
(define-fun mult_prob ((x Real) (y Real)) Real 
  (* x y)
)

(declare-datatype NodeMobile ((Rnode)))
(declare-datatype NodeInfra ((Anode) (Bnode) (Cnode)))
(declare-datatype NodeBase ((Dnode)))
(declare-datatype Node ((mobile (mnode NodeMobile)) (infra (inode NodeInfra)) (base (bnode NodeBase))))

(define-fun R () Node (mobile Rnode))
(define-fun A () Node (infra Anode))
(define-fun B () Node (infra Bnode))
(define-fun C () Node (infra Cnode))
(define-fun D () Node (base Dnode))

(declare-datatype RuleMobile ((R1) (R2)))
(declare-datatype RuleInfra ((R3)))
(declare-datatype Rule ((norule) (rulem (rulemrule RuleMobile)) (rulei (ruleirule RuleInfra))))

(declare-datatype Channel ((Ch1) (Ch2) (Ch3)))

(declare-datatype CellAssignMobile ((sleepm) (cam (cam_rule RuleMobile) (cam_ch Channel))))
(declare-datatype CellAssignInfra ((sleepi) (cai (cai_rule RuleInfra) (cai_ch Channel))))
 
; the global policy
(declare-fun policy_mobile (Int NodeMobile) CellAssignMobile)
(declare-fun policy_infra (Int NodeInfra) CellAssignInfra)

;; channel access predicate
; only one node can have access to a channel in a given time
; we map ( Channel, time ) to a single node
(declare-fun channel_access (Channel Int) Node)

;; subprocedures in rules
; argmax
(declare-fun argmax (Int) NodeInfra)
; global base station
(declare-fun global.bs () NodeBase)

; do we choose to send from Node send to Node rcv at given time?
(define-fun choose_transmit ((time Int) (send Node) (rcv Node)) Bool
  (or
  (and
    (is-mobile send)
    ; send has access to the channel at time
    (= (channel_access (cam_ch (policy_mobile time (mnode send))) time) send)
    ; and transmitmits to rcv
    (or 
      ; rule R2
      (and
        (is-cam (policy_mobile time (mnode send)))
        (= (cam_rule (policy_mobile time (mnode send))) R2)
        ; rcv must be an infrastructure node, the argmax
        (and (is-infra rcv) (= (argmax time) (inode rcv)))
      )
      ; other rules go here
    )
  )
  (and
    (is-infra send)
    ; send has access to the channel at time
    (= (channel_access (cai_ch (policy_infra time (inode send))) time) send)
    ; and transmitmits to rcv
    (or 
      ; rule R3
      (and 
        (is-cai (policy_infra time (inode send)))
        (= (cai_rule (policy_infra time (inode send))) R3)
        ; rcv must be a base node and the global base station
        (and (is-base rcv) (= global.bs (bnode rcv)))
      )
      ; other rules go here
    )
  ))
)

; connectivity
(define-fun connectivity ((time Int) (send Node) (rcv Node)) Real 0.75)
; the chance that send transmits to receiver at the given time
(define-fun do_transmit ((time Int) (send Node) (rcv Node)) Real
  (ite (= send rcv) 0.0 (ite (choose_transmit time send rcv) (connectivity time send rcv) 0.0))
)


; the energy consumed by a Node at a given time
(define-fun energy-consumed ((time Int) (x Node)) Real
(ite (is-mobile x) 
  ; sleepm costs 0, all others cost 1
  (ite (is-sleepm (policy_mobile time (mnode x))) 0.01 1.0)
(ite (is-infra x)
  ; sleepi costs 0.01, all others cost 1
  (ite (is-sleepi (policy_infra time (inode x))) 0.01 1.0)
; (is-base x)
  0.01)))


;;------------------------ state for each Node 
; chance we have transmitted to Node at a given time
(declare-fun transmit (Node Int) Real)
; how much energy we have consumed (cumulative) by a given time
(declare-fun energy (Node Int) Real)


;;----------------------- initial condition 
; we have transmitted to R only
(assert (= (transmit R 0) 1.0))
(assert (= (transmit A 0) 0.0))
(assert (= (transmit B 0) 0.0))
(assert (= (transmit C 0) 0.0))
(assert (= (transmit D 0) 0.0))

; energy consumption of all nodes is zero
(assert (= (energy R 0) 0.0))
(assert (= (energy A 0) 0.0))
(assert (= (energy B 0) 0.0))
(assert (= (energy C 0) 0.0))
(assert (= (energy D 0) 0.0))


;;-------------------- transition relation

; the chance that some node choose_transmit to rcv at a given time
(define-fun do_transmit_sum ((time Int) (rcv Node)) Real
    (sum_prob (mult_prob (transmit R time) (do_transmit time R rcv))
    (sum_prob (mult_prob (transmit A time) (do_transmit time A rcv)) 
    (sum_prob (mult_prob (transmit B time) (do_transmit time B rcv)) 
    (sum_prob (mult_prob (transmit C time) (do_transmit time C rcv)) 
              (mult_prob (transmit D time) (do_transmit time D rcv))))))
)
(declare-fun target_time () Int)
(assert (>= target_time 0))
(assert (forall ((x Node) (time Int))
(=> (and (<= 0 time) (< time target_time))
(and
  ; we have 
  (= (transmit x (+ time 1)) (sum_prob (transmit x time) (do_transmit_sum time x)))
  ; how energy updates
  (= (energy x (+ time 1)) (+ (energy x time) (energy-consumed time x)))
)
)))

;;-------------------- specification 
; must have a .8 chance of transmitting to D by the target time 
(assert (>= (transmit D target_time) 0.92))

; energy constraints
;(assert (<= (+ (energy R target_time) (energy A target_time) (energy B target_time) (energy C target_time) (energy D target_time)) 6.0))

; (symmetry breaking)
(assert (<= (transmit A target_time) (transmit B target_time)))
(assert (<= (transmit B target_time) (transmit C target_time)))
;(assert (<= (energy A target_time) (energy B target_time)))
;(assert (<= (energy B target_time) (energy C target_time)))

; time cannot be more than max period
(define-fun max_period () Int 6)
(assert (<= target_time max_period))

(declare-datatype Action ((na) (noact) (act (act_node Node) (act_rule Rule))))

;; the rule applied at a channel in a given time
(define-fun policy ((c Channel) (time Int)) Action
  (ite (>= time target_time) na
    (ite (is-mobile (channel_access c time))
      (ite (is-sleepm (policy_mobile time (mnode (channel_access c time))))
        noact
        (ite (= (cam_ch (policy_mobile time (mnode (channel_access c time)))) c)
          (act 
            (channel_access c time) 
            (rulem (cam_rule (policy_mobile time (mnode (channel_access c time)))))
          )
          noact
        ))
    (ite (is-infra (channel_access c time))
      (ite (is-sleepi (policy_infra time (inode (channel_access c time))))
        noact
        (ite (= (cai_ch (policy_infra time (inode (channel_access c time)))) c)
          (act 
            (channel_access c time) 
            (rulei (cai_rule (policy_infra time (inode (channel_access c time)))))
          )
          noact
        ))
    noact))
  )
)

(check-sat)
(get-model)
(get-value (target_time))
(get-value ((policy Ch1 0)))
(get-value ((policy Ch1 1)))
(get-value ((policy Ch1 2)))
(get-value ((policy Ch1 3)))
(get-value ((policy Ch1 4)))
(get-value ((policy Ch1 5)))
(get-value ((policy Ch2 0)))
(get-value ((policy Ch2 1)))
(get-value ((policy Ch2 2)))
(get-value ((policy Ch2 3)))
(get-value ((policy Ch2 4)))
(get-value ((policy Ch2 5)))
(get-value ((policy Ch3 0)))
(get-value ((policy Ch3 1)))
(get-value ((policy Ch3 2)))
(get-value ((policy Ch3 3)))
(get-value ((policy Ch3 4)))
(get-value ((policy Ch3 5)))
(get-value ((transmit R target_time) (energy R target_time)))
(get-value ((transmit A target_time) (energy A target_time)))
(get-value ((transmit B target_time) (energy B target_time)))
(get-value ((transmit C target_time) (energy C target_time)))
(get-value ((transmit D target_time) (energy D target_time)))
