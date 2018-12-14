(set-logic ALL)
(define-sort FP () (_ FloatingPoint 3 5))
(declare-fun f () FP)
(define-fun input 
() Bool ; __SIG
(=> 
;; the case of the IC we are currently solving:
true ; __SC
;; the invertibility condition problem we are solving:
(fp.isNormal (fp.abs f))  ; __PROBLEM
))

