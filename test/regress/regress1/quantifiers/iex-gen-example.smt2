; COMMAND-LINE: --iex-when=cinst
; EXPECT: unsat
(set-logic UFLIA)

(declare-fun Q (Int) Bool)
(declare-fun P (Int) Bool)
(declare-fun R (Int) Bool)
(declare-fun S (Int) Bool)
(declare-fun f (Int) Int)
(declare-fun a () Int)

(assert (forall ((x Int)) (not (Q x))))
(assert (forall ((w Int)) (not (R w))))

(assert (forall ((z Int)) (or (not (P z)) (S z) (P (+ 1 z)))))
(assert (forall ((y Int)) (or (Q y) (not (S y)) (R y))))

(assert (P a))
(assert (not (P 
(+ a 10)
)))
(check-sat)
