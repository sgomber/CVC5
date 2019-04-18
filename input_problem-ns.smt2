(set-logic BV)
(define-sort BV () (_ BitVec 8))
(get-invertibility-condition ((s BV) (t BV)) true (exists ((x BV)) (= (bvmul x s) t)))
