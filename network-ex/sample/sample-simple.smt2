(set-logic ALL)
(set-option :sampling true)

(declare-sample-sort UnifInt
  (
    (Start Int ((sample.int.unif 0 1000)))
  )
)

(declare-datatype D ((A) (B) (C) (D)))

(declare-fun g (D D) Int)
(declare-fun f (D D) UnifInt)

(assert (= (g A B) 750))
(assert (= (g A C) 500))
(assert (= (g B D) 100))
(assert (= (g C D) 500))


(define-fun sample_g ((x D) (y D)) Bool (> (g x y) (sample.run (f x y))))


(assert (or (sample_g A B) (sample_g A C)))
(assert (=> (sample_g A B) (sample_g B D)))
(assert (=> (sample_g A C) (sample_g C D)))

(check-sat)

