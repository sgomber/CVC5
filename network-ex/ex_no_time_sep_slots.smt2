(set-logic UFDTLIRA)
(set-option :fmf-bound true)
(set-option :produce-models true)

;;; ----- Agents (Nodes, Packets, Channels)

(declare-datatype NodeMobile ((Rnode)))
(declare-datatype NodeInfra ((Anode) (Bnode) (Cnode)))
(declare-datatype NodeBase ((Dnode)))
(declare-datatype Node ((mobile (mnode NodeMobile)) (infra (inode NodeInfra)) (base (bnode NodeBase))))

(define-fun R () Node (mobile Rnode))
(define-fun A () Node (infra Anode))
(define-fun B () Node (infra Bnode))
(define-fun C () Node (infra Cnode))
(define-fun D () Node (base Dnode))

(declare-datatype Packet ((P1)))

(declare-datatype Channel ((Ch1) (Ch2) (Ch3)))


;;; ----- The global state 


; for each packet, have we received that packet?
(declare-fun GlobalState_prcv (Node Packet Int) Bool)

; for each node, its energy consumption up to that time
(declare-fun GlobalState_energy (Node Int) Real)


;;; ----- Action, Conditionals

(declare-datatype Action
(
(act_idle)
(act_send (_dst Node) (_pck Packet) (_chn Channel))
))

(declare-datatype Condition
(
(ctrue) 
(cfalse)
(check_rcv (_rcv_pck Packet))
))

; --- does a condition hold for a Node at a given time, given the global state
(define-fun get-condition-holds ((c Condition) (n Node) (t Int)) Bool
  (ite ((_ is check_rcv) c)
    (GlobalState_prcv n (_rcv_pck c) t)
  (ite ((_ is ctrue) c) 
    true
  ; ((_ is cfalse) c)
    false)
  )
)
; --- 

;;; ----- Time

(declare-fun max_period () Int)
(assert (>= max_period 0))

;;; ----- The global policy 

(declare-fun GlobalPolicyCond (Node Int) Condition)
(declare-fun GlobalPolicyAct (Node Int) Action)

; --- get the action for a node at the given time, starting at slot s, given the GlobalPolicy
(declare-fun get-action-for-policy-slot (Node Int Int) Action)

; --- maximum number of slots
(declare-fun num_slots (Node) Int)
(assert (forall ((x Node)) (>= (num_slots x) 0)))
;(define-fun num_slots ((x Node)) Int 5)

(assert (forall ((n Node) (t Int) (s Int))
  (=>
    (and 
      (>= s 0) (<= s (num_slots n))
      (>= t 0) (< t max_period)
    )
    (= 
      (get-action-for-policy-slot n t s)
      (let ((c (GlobalPolicyCond n s)))
      ; if s is the max slot for n, or the condition holds
      (ite (or (= s (num_slots n)) (get-condition-holds c n t))
        ; if so, it is the conditional action
        (GlobalPolicyAct n s)
        ; otherwise, check the next slot
        (get-action-for-policy-slot n t (+ s 1))
      ))
    )
  )
))
(define-fun get-action ((n Node) (t Int)) Action
  ; get the action, starting from slot 0
  (get-action-for-policy-slot n t 0)
)
; --- 

;;; ----- Utilities for how actions update the state

; connected
(declare-fun connectivity (Node Node Int) Real)
(assert (forall ((x Node) (y Node) (t Int))
  (=>
    (and (>= t 0) (< t max_period))
    (= 
      (connectivity x y t)
      (ite (= x R)
        (ite (or (= y A) (= y B) (= y C)) 
          1.0
          0.0)
      (ite (or (= x A) (= x B) (= x C))
        (ite (= y D)
          1.0
          0.0)
      ;; (= x D)
        0.0))
    )
  )
))
(define-fun get-connected ((x Node) (y Node) (t Int)) Bool 
;; TODO: take into account connectivity
  true
)

; was the action successful?
(define-fun get-act-success ((x Node) (t Int)) Bool
  (let ((x_act_at_t (get-action x t)))
  (ite ((_ is act_send) x_act_at_t)
    (and 
      ; must be connected to destination at that time
      (get-connected x (_dst x_act_at_t) t) 
      ; packet must have already been received by x
      (GlobalState_prcv x (_pck x_act_at_t) t)
      ; must be the user of the channel at this time
      ;(= (get-channel-use (_chn x_act_at_t) t) x)
    )
    true
  )
  )
)

; holds if x sends packet p to y at time t
(define-fun get-sends ((x Node) (y Node) (p Packet) (t Int)) Bool
  (let ((x_act_at_t (get-action x t)))
  (and
    (ite ((_ is act_send) x_act_at_t)
      ; packet must be p and destination must be y
      (and 
        (= (_dst x_act_at_t) y)
        (= (_pck x_act_at_t) p)
      )
      false
    )
    (get-act-success x t)
  ))
)

; get energy consumption
(define-fun get-energy ((x Node) (t Int)) Real
  (let ((x_act_at_t (get-action x t)))
  (ite ((_ is act_send) x_act_at_t)
    1.0
    0.05
  ))
)

;;; ----- Initial state

; R has all packets, no one else has any packet
(assert (forall ((n Node) (p Packet)) (= (GlobalState_prcv n p 0) (= n R))))
(assert (forall ((n Node)) (= (GlobalState_energy n 0) 0.0)))

;;; ----- Transition relation 

(assert 
(forall ((x Node) (t Int))
(=>
  (and (>= t 0) (< t max_period))
  (and
    (forall ((p Packet))
      (= 
        (GlobalState_prcv x p (+ t 1)) 
        (or 
          (GlobalState_prcv x p t)
          (exists ((y Node)) (get-sends y x p t)))
      )
    )
    (=
      (GlobalState_energy x (+ t 1))
      (+ (GlobalState_energy x t) (get-energy x t))
    )
  )
))
)

;;; ----- Validity of actions
(assert
(forall ((x Node) (y Node) (t Int))
  (let ((x_act_at_t (get-action x t)))
  (let ((y_act_at_t (get-action y t)))
  (=>
    (and (>= t 0) (< t max_period) (not (= x y)))
    (=>
      (and ((_ is act_send) x_act_at_t) ((_ is act_send) y_act_at_t))
      (not (= (_chn x_act_at_t) (_chn y_act_at_t)))
    )
  )))
))


;;; ----- Requirements

(assert (GlobalState_prcv D P1 max_period))
;(assert (< (GlobalState_energy R max_period) 2.0))
;(assert (< (GlobalState_energy A max_period) 2.0))
;(assert (< (GlobalState_energy B max_period) 2.0))
;(assert (< (GlobalState_energy C max_period) 2.0))
;(assert (< (GlobalState_energy D max_period) 2.0))

(check-sat)

;;; ---- For pretty printing

(declare-datatype PrintAction
(
(act_invalid)
(do_act (_pact Action))
))
(define-fun get-paction ((x Node) (t Int)) PrintAction
  (ite (>= t max_period)
    act_invalid
    (do_act (get-action x t))
  )
)
(define-fun get-penergy ((x Node) (t Int)) Real
  (GlobalState_energy R (ite (>= t max_period) max_period t))
)

(get-value (max_period))
(get-value ((get-paction R 0)))
(get-value ((get-paction R 1)))
(get-value ((get-paction R 2)))
(get-value ((get-paction R 3)))
(get-value ((get-paction R 4)))
(get-value ((get-paction A 0)))
(get-value ((get-paction A 1)))
(get-value ((get-paction A 2)))
(get-value ((get-paction A 3)))
(get-value ((get-paction A 4)))
(get-value ((get-paction B 0)))
(get-value ((get-paction B 1)))
(get-value ((get-paction B 2)))
(get-value ((get-paction B 3)))
(get-value ((get-paction B 4)))
(get-value ((get-paction C 0)))
(get-value ((get-paction C 1)))
(get-value ((get-paction C 2)))
(get-value ((get-paction C 3)))
(get-value ((get-paction C 4)))
(get-value ((get-paction D 0)))
(get-value ((get-paction D 1)))
(get-value ((get-paction D 2)))
(get-value ((get-paction D 3)))
(get-value ((get-paction D 4)))
(get-value ((GlobalState_energy R max_period)))
(get-value ((GlobalState_energy A max_period)))
(get-value ((GlobalState_energy B max_period)))
(get-value ((GlobalState_energy C max_period)))
(get-value ((GlobalState_energy D max_period)))

(get-value ((GlobalPolicy R 0)))
