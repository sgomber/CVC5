(set-logic ALL)

(declare-datatype Node ((A) (B) (C)))

; (transmits x t) holds if Node x transmits at time t
(declare-fun transmits (Node Int) Bool)


; the number of transmissions by a given time
(declare-fun num_transmits (Node Int) Int)

(assert (forall ((x Node)) (= (num_transmits x 0) 0)))

(declare-fun max_period () Int)
(assert (>= max_period 0))

(assert 
  (forall ((x Node) (t Int)) 
    (=> (and (<= 0 t) (< t max_period)) 
      (= (num_transmits x (+ t 1)) (+ (num_transmits x t) (ite (transmits x t) 1 0))))))

; requirement

(assert (forall ((x Node)) (>= (num_transmits x max_period) 3)))

(check-sat)
