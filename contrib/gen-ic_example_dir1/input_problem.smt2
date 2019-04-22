(set-logic ALL)
(define-sort FP () (_ FloatingPoint 3 5))
(declare-fun IC (FP) Bool)
(assert (forall ((s FP)) (=> true (= (IC s) (exists ((x FP)) (fp.isNormal (fp.add RNA x s)))))))
