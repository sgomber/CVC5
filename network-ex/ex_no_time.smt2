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

(declare-datatype ConditionAtom
(
(ctrue)
(check_rcv (_rcv_pck Packet))
))

(declare-datatype Condition
(
(c_atom (_catom_arg ConditionAtom))
(c_atom_not (_catom_not_arg ConditionAtom))
))

; --- get the fixed pre-condition for doing the action
(define-fun get-precondition-for-action ((a Action)) Condition
  ; if sending, should always check received
  (ite ((_ is act_send) a) (c_atom (check_rcv (_pck a)))
  ; otherwise no pre-condition
     (c_atom ctrue)
))

; --- does a condition hold for a Node at a given time, given the global state
(define-fun get-condition-atom-holds ((c ConditionAtom) (n Node) (t Int)) Bool
  (ite ((_ is check_rcv) c)
    (GlobalState_prcv n (_rcv_pck c) t)
  (ite ((_ is ctrue) c) 
    true
    false)
  )
)
(define-fun get-condition-holds ((c Condition) (n Node) (t Int)) Bool
  (ite ((_ is c_atom) c)
    (get-condition-atom-holds (_catom_arg c) n t)
  (ite ((_ is c_atom_not) c) 
    (get-condition-atom-holds (_catom_not_arg c) n t)
    false)
  )
)
; --- 

;;; ----- Time

(declare-fun max_period () Int)
(assert (>= max_period 0))

;;; ----- The global policy 

; A "policy" is a sequence of conditional actions.
; A "slot" is a line number in this sequence.
; The two definitions below define a policy.

; maps (Nodes, Slots) to the action taken in this slot
(declare-fun GlobalPolicyAct (Node Int) Action)

; maps (Nodes, Slots) to the conditional under which the action in this slot is taken
(declare-fun GlobalPolicyCond (Node Int) Condition)

; --- information about slots
(declare-fun max_slots () Int)
(assert (>= max_slots 0))

;(declare-fun num_slots (Node) Int)
;(assert (forall ((x Node)) (>= (num_slots x) 0)))
;(define-fun num_slots ((x Node)) Int 5)

; --- always terminate with true condition
(assert (forall ((x Node)) (= (GlobalPolicyCond x max_slots) (c_atom ctrue))))
(assert (forall ((x Node)) (= (get-precondition-for-action (GlobalPolicyAct x max_slots)) (c_atom ctrue))))

; --- get the action for a node at the given time, starting at slot s, given the GlobalPolicy
; this depends on which condition holds
(declare-fun get-action-for-time-slot (Node Int Int) Action)
(assert (forall ((x Node) (t Int) (s Int))
  (=>
    (and 
      (>= s 0) (<= s max_slots)
      (>= t 0) (< t max_period)
    )
    (= 
      (get-action-for-time-slot x t s)
      (let ((c (GlobalPolicyCond x s)))
      (let ((cp (get-precondition-for-action (GlobalPolicyAct x s))))
      ; if s is the max slot for x, or the condition holds
      (ite (and (get-condition-holds c x t) (get-condition-holds cp x t))
        ; if so, it is the conditional action
        (GlobalPolicyAct x s)
        ; otherwise, check the next slot
        (get-action-for-time-slot x t (+ s 1))
      )))
    )
  )
))
(define-fun get-action ((x Node) (t Int)) Action
  ; get the action, starting from slot 0
  (get-action-for-time-slot x t 0)
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
        (ite (= y A) 0.9
        (ite (= y B) 0.5
        (ite (= y C) 0.3
          0.0)))
      (ite (= x A) 
        (ite (= y D) 0.1 0.0)
      (ite (= x B) 
        (ite (= y D) 0.9 0.0)
      (ite (= x C) 
        (ite (= y D) 0.8 0.0)

        0.0))))
    )
  )
))

;(sample-sort UnifReal Real
;  ((Start Real ((/ (random.unif 0 10000) 10000))))
;)

; (declare-datatype Enum ((A) (B)))

;(sample-sort sampleAB Enum (Start)
; ((Start Enum ((! A :probability .4) (! B :probability .6))))
;)
;(declare-fun sample-var () sampleAB)


;(declare-fun sample-connectivity (Node Node Int) UnifReal)
(declare-fun sample-connectivity (Node Node Int) Real)

; the chance that the action successful
(define-fun get-act-success ((x Node) (t Int)) Bool
  (let ((x_act_at_t (get-action x t)))
  (let ((y (_dst x_act_at_t)))
  (ite ((_ is act_send) x_act_at_t)
    ; packet must have already been received by x
    (ite (GlobalState_prcv x (_pck x_act_at_t) t)
      ; must be connected to destination at that time
      (> (connectivity x y t) (sample-connectivity x y t)) 
      false
    )
    true
  )))
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
(assert (forall ((x Node) (p Packet)) (= (GlobalState_prcv x p 0) (= x R))))
(assert (forall ((x Node)) (= (GlobalState_energy x 0) 0.0)))

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

; cannot use the same channel
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

; cannot send packets you don't have
(assert
(forall ((x Node) (t Int))
  (let ((x_act_at_t (get-action x t)))
  (=>
    (and (>= t 0) (< t max_period))
    (=>
      ((_ is act_send) x_act_at_t) 
      (GlobalState_prcv x (_pck x_act_at_t) t)
    )
  ))
))



;;; ----- Requirements

(assert (GlobalState_prcv D P1 max_period))
(assert (< (GlobalState_energy R max_period) 3.0))
(assert (< (GlobalState_energy A max_period) 3.0))
(assert (< (GlobalState_energy B max_period) 3.0))
(assert (< (GlobalState_energy C max_period) 3.0))
(assert (< (GlobalState_energy D max_period) 3.0))

(check-sat)

;;; ---- For pretty printing

(declare-datatype PrintAction
(
(act_none)
(do_act (_pact Action))
))
(define-fun print-action ((x Node) (t Int)) PrintAction
  (ite (>= t max_period)
    act_none
    (do_act (get-action x t))
  )
)
(define-fun print-energy ((x Node) (t Int)) Real
  (GlobalState_energy x (ite (>= t max_period) max_period t))
)

(declare-datatype PrintPolicy
(
  (policy_none)
  (policy_conditional_act (_cac Condition) (_caa Action))
  (policy_act (_aa Action))
)
)
(define-fun print-policy ((x Node) (s Int)) PrintPolicy
  (ite (> s max_slots)
    policy_none
  (ite (= s max_slots)
    (policy_act (GlobalPolicyAct x s))
    (policy_conditional_act (GlobalPolicyCond x s) (GlobalPolicyAct x s))
  ))
)

(get-value (max_period))
(get-value ((print-action R 0)))
(get-value ((print-action R 1)))
(get-value ((print-action R 2)))
(get-value ((print-action R 3)))
(get-value ((print-action R 4)))
(get-value ((print-action A 0)))
(get-value ((print-action A 1)))
(get-value ((print-action A 2)))
(get-value ((print-action A 3)))
(get-value ((print-action A 4)))
(get-value ((print-action B 0)))
(get-value ((print-action B 1)))
(get-value ((print-action B 2)))
(get-value ((print-action B 3)))
(get-value ((print-action B 4)))
(get-value ((print-action C 0)))
(get-value ((print-action C 1)))
(get-value ((print-action C 2)))
(get-value ((print-action C 3)))
(get-value ((print-action C 4)))
(get-value ((print-action D 0)))
(get-value ((print-action D 1)))
(get-value ((print-action D 2)))
(get-value ((print-action D 3)))
(get-value ((print-action D 4)))
(get-value ((print-energy R max_period)))
(get-value ((print-energy A max_period)))
(get-value ((print-energy B max_period)))
(get-value ((print-energy C max_period)))
(get-value ((print-energy D max_period)))

; the policy
(get-value (max_slots))
(get-value ((print-policy R 0)))
(get-value ((print-policy R 1)))
(get-value ((print-policy R 2)))
(get-value ((print-policy R 3)))
(get-value ((print-policy R 4)))
(get-value ((print-policy A 0)))
(get-value ((print-policy A 1)))
(get-value ((print-policy A 2)))
(get-value ((print-policy A 3)))
(get-value ((print-policy A 4)))
(get-value ((print-policy B 0)))
(get-value ((print-policy B 1)))
(get-value ((print-policy B 2)))
(get-value ((print-policy B 3)))
(get-value ((print-policy B 4)))
(get-value ((print-policy C 0)))
(get-value ((print-policy C 1)))
(get-value ((print-policy C 2)))
(get-value ((print-policy C 3)))
(get-value ((print-policy C 4)))
(get-value ((print-policy D 0)))
(get-value ((print-policy D 1)))
(get-value ((print-policy D 2)))
(get-value ((print-policy D 3)))
(get-value ((print-policy D 4)))
