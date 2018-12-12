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
(declare-datatype Node ((nonode) (mobile (mnode NodeMobile)) (infra (inode NodeInfra)) (base (bnode NodeBase))))

(define-fun R () Node (mobile Rnode))
(define-fun A () Node (infra Anode))
(define-fun B () Node (infra Bnode))
(define-fun C () Node (infra Cnode))
(define-fun D () Node (base Dnode))

(declare-datatype RuleMobile ((R1) (R2)))
(declare-datatype RuleInfra ((R3)))
(declare-datatype Rule ((norule) (rulem (rulemrule RuleMobile)) (rulei (ruleirule RuleInfra))))

(declare-datatype Action
  ((na) 
   (noact)
   (actm (amnode NodeMobile) (amrule RuleMobile))
   (acti (ainode NodeInfra) (airule RuleInfra))
  )
)
(define-fun ActionToNode ((act Action)) Node
  (ite (is-actm act) (mobile (amnode act))
  (ite (is-acti act) (infra (ainode act))
    nonode)))
(define-fun ActionToRule ((act Action)) Rule
  (ite (is-actm act) (rulem (amrule act))
  (ite (is-acti act) (rulei (airule act))
    norule)))
    
; the action sequence and its length
(declare-fun act_seq (Int) Action)
(declare-fun act_seq_l () Int)
(assert (>= act_seq_l 0))
; the actual sequence
(define-fun actualActionSeq ((time Int)) Action
  (ite (and (<= 0 time) (< time act_seq_l)) (act_seq time) na))


;; subprocedures in rules
; argmax
(declare-fun argmax (Int) NodeInfra)
; global base station
(declare-fun global.bs () NodeBase)

; do we choose to send from Node send to Node rcv at given time?
(define-fun choose_transmit ((time Int) (send Node) (rcv Node)) Bool
(let ((act (act_seq time)))
  (and (not (= send rcv))
    (or
    (and
      (is-actm act)
      (is-mobile send)
      (= (amnode act) (mnode send))
      ; and transmitmits to rcv
      (or 
        ; rule R2
        (and
          (= (amrule act) R2)
          ; rcv must be an infrastructure node, the argmax
          (and (is-infra rcv) (= (argmax time) (inode rcv)))
        )
        ; other rules go here
      )
    )
    (and
      (is-acti act)
      ; 
      (is-infra send)
      (= (ainode act) (inode send))
      ; and transmitmits to rcv
      (or 
        ; rule R3
        (and 
          (= (airule act) R3)
          ; rcv must be a base node and the global base station
          (and (is-base rcv) (= global.bs (bnode rcv)))
        )
        ; other rules go here
      )
    ))
)))

; connectivity
(define-fun connectivity ((time Int) (send Node) (rcv Node)) Real 0.75)
; the chance that send transmits to receiver at the given time
(define-fun do_transmit ((time Int) (send Node) (rcv Node)) Real
  (ite (choose_transmit time send rcv) 
    (connectivity time send rcv) 0.0)
)


; the energy consumed by a Node at a given time
(define-fun energy-consumed ((time Int) (x Node)) Real
; if the action sequence involves this node
(let ((act (act_seq time)))
  (ite (= (ActionToNode act) x) 1.0 0.0)))


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
(assert (= target_time act_seq_l))
(assert (forall ((x Node) (time Int))
(=> (and (<= 0 time) (< time act_seq_l))
(and
  ; we have 
  (= (transmit x (+ time 1)) (sum_prob (transmit x time) (do_transmit_sum time x)))
  ; how energy updates
  (= (energy x (+ time 1)) (+ (energy x time) (energy-consumed time x)))
)
)))

;;-------------------- specification 
; must have a .8 chance of transmitting to D by the target time 
(assert (>= (transmit D target_time) 0.6))

; energy constraints
(assert (<= (+ (energy R target_time) (energy A target_time) (energy B target_time) (energy C target_time) (energy D target_time)) 6.0))

; (symmetry breaking)
(assert (<= (transmit A target_time) (transmit B target_time)))
(assert (<= (transmit B target_time) (transmit C target_time)))
;(assert (<= (energy A target_time) (energy B target_time)))
;(assert (<= (energy B target_time) (energy C target_time)))

; time cannot be more than max period
(define-fun max_period () Int 6)
(assert (<= target_time max_period))




(check-sat)
(get-model)
(get-value (target_time))
(get-value ((actualActionSeq 0)))
(get-value ((actualActionSeq 1)))
(get-value ((actualActionSeq 2)))
(get-value ((actualActionSeq 3)))
(get-value ((actualActionSeq 4)))
(get-value ((actualActionSeq 5)))
(get-value ((transmit R target_time) (energy R target_time)))
(get-value ((transmit A target_time) (energy A target_time)))
(get-value ((transmit B target_time) (energy B target_time)))
(get-value ((transmit C target_time) (energy C target_time)))
(get-value ((transmit D target_time) (energy D target_time)))
