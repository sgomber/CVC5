(set-logic ALL)
(set-option :sampling true)

(sample-sort UnifInt
  (
    (Start Int ((sample.int.unif 0 1000)))
  )
)

(declare-fun g (Int) Int)
(declare-fun f (Int) UnifInt)

(assert (= (g 0) 750))
(assert (= (g 1) 500))
(assert (= (g 2) 500))
(assert (= (g 3) 100))


(define-fun sample_g ((x Int)) Bool (> (g x) (sample.run (f x))))


(assert (or (sample_g 0) (sample_g 1)))
(assert (=> (sample_g 0) (sample_g 2)))
(assert (=> (sample_g 1) (sample_g 3)))

(check-sat)

