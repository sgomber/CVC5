(set-logic QF_UFDT)

(declare-datatype Node ((A) (B) (C) (D)))

; policies
(declare-fun pA (Bool Bool Bool Bool) Node)
(declare-fun pB (Bool Bool Bool Bool) Node)
(declare-fun pC (Bool Bool Bool Bool) Node)
(declare-fun pD (Bool Bool Bool Bool) Node)

; transition relation T
(define-fun T ((transA Bool) (transB Bool) (transC Bool) (transD Bool) (transAp Bool) (transBp Bool) (transCp Bool) (transDp Bool)) Bool
(and
  (= transA transAp)
  (= (or transB (and transA (= (pA transA transB transC transD) B) (= (pB transA transB transC transD) A))) transBp)
  (= (or transC (and transB (= (pB transA transB transC transD) C) (= (pC transA transB transC transD) B))) transCp)
  (= (or transD (and transC (= (pC transA transB transC transD) D) (= (pD transA transB transC transD) C))) transDp)
))


(declare-fun transA0 () Bool)
(declare-fun transB0 () Bool)
(declare-fun transC0 () Bool)
(declare-fun transD0 () Bool)

; initial condition
(assert transA0)
(assert (not transB0))
(assert (not transC0))
(assert (not transD0))


; unfold 1
(declare-fun transA1 () Bool)
(declare-fun transB1 () Bool)
(declare-fun transC1 () Bool)
(declare-fun transD1 () Bool)
(assert (T transA0 transB0 transC0 transD0 transA1 transB1 transC1 transD1))


; unfold 2
(declare-fun transA2 () Bool)
(declare-fun transB2 () Bool)
(declare-fun transC2 () Bool)
(declare-fun transD2 () Bool)
(assert (T transA1 transB1 transC1 transD1 transA2 transB2 transC2 transD2))


; unfold 3
(declare-fun transA3 () Bool)
(declare-fun transB3 () Bool)
(declare-fun transC3 () Bool)
(declare-fun transD3 () Bool)
(assert (T transA2 transB2 transC2 transD2 transA3 transB3 transC3 transD3))


; specification: may have transmitted to D by time 3
(assert transD3)

(check-sat)
(get-model)


