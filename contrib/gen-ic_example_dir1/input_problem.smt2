(set-logic ALL)
(define-sort FP () (_ FloatingPoint 3 5))
(declare-const s FP)
(declare-fun f (FP) FP)
(define-fun input 
((s FP)) Bool ; __SIG
(=> 
;; the case of the IC we are currently solving:
true ; __SC
;; the invertibility condition problem we are solving:
(fp.isNormal (fp.add RNA (f s) s))  ; __PROBLEM
))

