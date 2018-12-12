(set-logic ALL)
(set-option :sampling true)
(set-option :num-samples 1000)
(set-option :num-samples-sat 999)

(declare-datatype Enum ((A) (B) (C) (D)))

(declare-fun x () Enum)
(declare-fun f (Enum) Enum)

(sample-sort RandomEnum Enum
(
  (Start Enum (A B C x (f Start)))
)
)

(declare-fun random () RandomEnum)

(declare-fun y () Enum)
(assert (not (= y (sample.run random))))

(assert (= (f D) D))

(check-sat)
