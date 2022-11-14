(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun u () String)

(assert
(str.in_re w (re.++ (re.* re.allchar) (str.to_re "ABC"))))

(assert
(or
  (= w (str.++ x u y z))
  (= w (str.++ z u y x))
  (= w (str.++ x u z y))
  (= w (str.++ x z u y))
)
)

(assert (not (= u "")))

(assert
(or (= x "D") (= x "E") (= x "F"))
)
(assert
(or (= y "D") (= y "E") (= y "F"))
)
(assert
(or (= z "D") (= z "E") (= z "F"))
)

(check-sat)
