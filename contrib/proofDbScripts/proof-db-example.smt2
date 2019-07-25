(declare-fun flatten (String) String)
(proof-db (
  (x String) (y String) (z String)
) (
  len-concat (=> true (= (str.len (str.++ x y)) (+ (str.len x) (str.len y))))
  prefix-elim (=> true (= (str.prefixof x y) (= x (str.substr y 0 (str.len x)))))
  re-in-const-str (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  re-all-char (=> true (= (str.in.re x (re.* re.allchar)) true))
  empty-concat (=> true (= (str.++ "" x) x))
  flatten-concat (=> (= (flatten (str.++ x y)) z) (= (str.++ x y) z))
))
