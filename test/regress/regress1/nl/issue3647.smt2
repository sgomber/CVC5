; COMMAND-LINE: --no-check-models --produce-models --decision=internal --nl-rlv=always
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(assert (distinct (sin 1.0) 0.0))
(check-sat)
