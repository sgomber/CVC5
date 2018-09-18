; COMMAND-LINE: --rewrite-divk --nl-ext-tplanes-limit=0
; EXPECT: unknown
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= 1 (mod (* x y) 3)))
(check-sat)
(exit)
