(set-logic ALL)
(define-sort FP () (_ FloatingPoint 3 5))
(declare-const s FP)
(declare-const t FP)
(declare-fun f (FP FP) FP)
(define-fun input 
((s FP) (t FP)) Bool ; __SIG
(=> 
;; the case of the IC we are currently solving:
(fp.isNormal s) ; __SC
;; the invertibility condition problem we are solving:
(= (fp.add RNE (f s t) s) t) ; __PROBLEM
))

