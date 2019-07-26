(declare-fun flatten (String) String)
(proof-db (
  (x String) (y String) (z String) (n Int) (m Int) (r RegLan) (s RegLan)
) (
  len-concat (=> true (= (str.len (str.++ x y)) (+ (str.len x) (str.len y))))
  prefix-elim (=> true (= (str.prefixof x y) (= x (str.substr y 0 (str.len x)))))
  str.at-elim (=> true (= (str.at x n) (str.substr x n 1)))
  re-in-const-str (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  re-all-char (=> true (= (str.in.re x (re.* re.allchar)) true))
  empty-concat (=> true (= (str.++ "" x) x))
  flatten-concat (=> (= (flatten (str.++ x y)) z) (= (str.++ x y) z))
  repl-id (=> true (= (str.replace x x y) y))
  repl-idem (=> true (= (str.replace x y y) x))
  repl-no (=> (= (str.contains x y) false) (= (str.replace x y z) x))
  repl-empty (=> true (= (str.replace x "" y) (str.++ y x)))
  repl-empty-inv (=> true (= (str.replace "" x "") ""))
  substr-neg (=> (= (> 0 n) true) (= (str.substr x n m) ""))
  substr-oob (=> (= (>= n (str.len x)) true) (= (str.substr x n m) ""))
  ctn-empty (=> true (= (str.contains x "") true))
  ctn-to-eq (=> true (= (str.contains "" x) (= "" x)))
  ctn-len (=> (= (> (str.len y) (str.len x)) true) (= (str.contains x y) false))
  indexof-nctn (=> (= (str.contains x y) false) (= (str.indexof x y n) (- 1)))
  indexof-neg (=> (= (> 0 n) true) (= (str.indexof x y n) (- 1)))
  indexof-oob (=> (= (> n (str.len x)) true) (= (str.indexof x y n) (- 1)))
  indexof-pos (=> true (= (> 0 (str.indexof x y n)) false))
  
  ; re-loop-elim (exists ((r RegLen)) (re.loop r n m))
  ; re-loop-elim (re.loop r (const n) (const m)) ----> t[r]
  ;              (re.loop C (const n) (const m)) ----> t[C]  /  s
  ; plus-eval (+ (const n) (const m))
  ; plus-eval2 (=> (= (Rewriter::rewrite (+ (const n) (const m))) e) (= (+ (const n) (const m)) e))
))

; via-rewrite (=> (= (rewrite x) y) (= x y))
