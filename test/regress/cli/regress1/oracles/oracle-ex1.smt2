(set-logic ALL)
(set-option :produce-models true)
(declare-fun input () Int)
(declare-oracle-fun f (Int) Bool isPrime)
(assert (f input))
(assert (> input 30000))
; find a prime greater than 30000
(check-sat)
(get-value (input))
