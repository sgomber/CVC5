(set-logic ALL)
(set-option :produce-models true)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-oracle-fun is-p (Int) Bool isPrime)
(assert (and (is-p c) (is-p d) (<= 2 c) (< c d) (< d 10)))
; find two distinct primes within the given bounds
(check-sat)
(get-value (c d))
