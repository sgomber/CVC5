; COMMAND-LINE: --nl-ext --nl-ext-tplanes
; EXPECT: sat
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-fun x () Int)
(assert (= (- 3 (* (div 3 x) x)) (mod 3 x)))
(check-sat)
