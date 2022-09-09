; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-fun s () Bool)
(assert (or (not s) (> (ite x 0 1) 1)))
(push)
(assert s)
(check-sat)
(pop)
(push)
(assert s)
(check-sat)
(pop)
(assert (or s (> (ite x 0 1) 1)))
(check-sat)
