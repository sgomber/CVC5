(set-logic QF_LIA)
(set-option :produce-abducts true)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (> x 0))

;(get-abduct A (> y 0))
(get-weak-abduct A (> y 0) (> (+ x y) 2))
