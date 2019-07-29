(declare-fun flatten_string (String) String)
(declare-fun flatten_bool (Bool) Bool)
(declare-fun flatten_regexp (RegLan) RegLan)
(declare-fun arith_norm_term (Int) Int)
(declare-fun arith_norm_term_abs (Int) Int)
(proof-db (
  (x String) (y String) (z String) (w String)
  (n Int) (m Int) (o Int) (p Int) 
  (r RegLan) (s RegLan) (t RegLan)
  (b Bool) (c Bool) (d Bool)
) (
  ;len-concat (=> true (= (str.len (str.++ x y)) (+ (str.len x) (str.len y))))
  ; general form needed since rewriter takes "shortcuts" like (str.len (str.++ x "A")) ---> (+ (str.len x) 1)
  len-concat-gen (=> (and (= (str.len x) n) (= (str.len y) m)) (= (str.len (str.++ x y)) (+ n m)))
  
  len-repl-inv (=> (= (= (str.len y) (str.len z)) true) (= (str.len (str.replace x y z)) (str.len x)))
  
  prefixof-elim (=> true (= (str.prefixof x y) (= x (str.substr y 0 (str.len x)))))
  suffixof-elim (=> true (= (str.suffixof x y) (= x (str.substr y (- (str.len y) (str.len x)) (str.len x)))))
  str.at-elim (=> true (= (str.at x n) (str.substr x n 1)))
  
  re-in-const-str (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  re-all-char (=> true (= (str.in.re x (re.* re.allchar)) true))
  re-concat-nctn (=> (= (>= (str.len y) (+ (str.len x) 1)) true) (= (str.in.re x (re.++ (str.to.re y) s)) false))
  
  ; recursion builtin
  re-union (=> (= (str.in.re x s) b) (= (str.in.re x (re.union r s)) (or (str.in.re x r) b)))
  re-inter (=> (= (str.in.re x s) b) (= (str.in.re x (re.inter r s)) (and (str.in.re x r) b)))
  
  re-concat-find (=> (and (= (str.in.re x r) true) (= (str.in.re "" s) true)) (= (str.in.re x (re.++ r s)) true))
  re-concat-skip (=> (and (= (str.in.re "" r) true) (= (str.in.re x s) true)) (= (str.in.re x (re.++ r s)) true))
  re-concat (=> (and (= (str.in.re x r) true) (= (str.in.re y s) true)) (= (str.in.re (str.++ x y) (re.++ r s)) true))
  re-consume (=> (= (str.in.re y (re.++ (str.to.re z) r)) b) (= (str.in.re (str.++ x y) (re.++ (str.to.re (str.++ x z)) r)) b))
  re-consume-sing (=> (= (str.in.re y r) b) (= (str.in.re (str.++ x y) (re.++ (str.to.re x) r)) b))
  re-consume-sing-sing (=> (= (str.in.re "" r) b) (= (str.in.re x (re.++ (str.to.re x) r)) b))
  
  re-clash (=> (and (= (= (str.len x) (str.len y)) true) (= (= x y) false)) (= (str.in.re (str.++ x z) (re.++ (str.to.re (str.++ y w)) r)) false))
  
  re-str-to-re-true (=> true (= (str.in.re x (str.to.re x)) true))
  re-str-to-re-eq (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  
  re-union-find (=> (= (str.in.re x r) true) (= (str.in.re x (re.union r s)) true))
  re-union-skip (=> (= (str.in.re x s) true) (= (str.in.re x (re.union r s)) true))
  re-emp-in-star (=> true (= (str.in.re "" (re.* r)) true))
  
  re-concat-nostr (=> true (= (re.++ r re.nostr) re.nostr))
  re-concat-nostr2 (=> true (= (re.++ re.nostr r) re.nostr))
  re-star-nostr (=> true (= (re.* re.nostr) (str.to.re "")))
  
  re-concat-flatten (=> (= (flatten_regexp (re.++ r s)) t) (= (re.++ r s) t))
  
  ;empty-concat (=> true (= (str.++ "" x) x))
  concat-flatten (=> (= (flatten_string (str.++ x y)) z) (= (str.++ x y) z))
  repl-id (=> true (= (str.replace x x y) y))
  repl-idem (=> true (= (str.replace x y y) x))
  repl-no (=> (= (str.contains x y) false) (= (str.replace x y z) x))
  repl-empty (=> true (= (str.replace x "" y) (str.++ y x)))
  repl-empty-inv (=> true (= (str.replace "" x "") ""))
  substr-emp (=> true (= (str.substr "" n m) ""))
  substr-id (=> (= n (str.len x)) (= (str.substr x 0 n) x))
  substr-neg (=> (= (>= 0 (+ n 1)) true) (= (str.substr x n m) ""))
  substr-range (=> (= (>= 0 m) true) (= (str.substr x n m) ""))
  substr-oob (=> (= (>= n (str.len x)) true) (= (str.substr x n m) ""))
  
  substr-concat-ctn (=> (= (>= (str.len x) (+ n m)) true) (= (str.substr (str.++ x y) n m) (str.substr x n m)))
  substr-concat-nctn (=> (and (= (>= n (str.len x)) true) (= (- n (str.len x)) o)) (= (str.substr (str.++ x y) n m) (str.substr y o m)))
  
  ctn-empty (=> true (= (str.contains x "") true))
  ctn-to-eq-e (=> true (= (str.contains "" x) (= "" x)))
  ctn-to-eq (=> (= (>= (str.len y) (str.len x)) true) (= (str.contains x y) (= x y)))
  ctn-len (=> (= (>= (str.len y) (+ (str.len x) 1)) true) (= (str.contains x y) false))
  
  indexof-find (=> true (= (str.indexof (str.++ x y) x 0) 0))
  indexof-find-sing (=> true (= (str.indexof x x 0) 0))
  indexof-nctn (=> (= (str.contains x y) false) (= (str.indexof x y n) (- 1)))
  indexof-neg (=> (= (> 0 n) true) (= (str.indexof x y n) (- 1)))
  indexof-oob (=> (= (> n (str.len x)) true) (= (str.indexof x y n) (- 1)))
  indexof-pos (=> true (= (> 0 (str.indexof x y n)) false))
  indexof-id (=> true (= (str.indexof x x n) (str.indexof "" "" n)))
  
  
  index-lb (=> true (= (>= (str.indexof x y n) (- 1)) true))
  index-ub (=> (= (str.len x) m) (= (>= m (str.indexof x y n)) true))
  len-lb (=> true (= (>= (str.len x) 0) true))
  
  arith-norm-lt (=> true (= (< n m) (not (>= n m))))
  arith-norm-term (=> (= (arith_norm_term n) (arith_norm_term m)) (= n m))
  arith-norm-eq (=> (= (arith_norm_term_abs (- n m)) (arith_norm_term_abs (- o p))) (= (= n m) (= o p)))
  arith-norm-geq (=> (= (arith_norm_term (- n m)) (arith_norm_term (- o p))) (= (>= n m) (>= o p)))
  arith-norm-geq-ngeq (=> (= (arith_norm_term (- n m)) (arith_norm_term (- p (+ o 1)))) (= (>= n m) (not (>= o p))))
  arith-norm-leq (=> (= (arith_norm_term (- n m)) (arith_norm_term (- o p))) (= (<= n m) (<= o p)))
  arith-norm-leq-ngeq (=> (= (arith_norm_term (- m n)) (arith_norm_term (- p (+ o 1)))) (= (<= n m) (not (>= o p))))
  arith-norm-leq-geq (=> (= (arith_norm_term (- m n)) (arith_norm_term (- o p))) (= (<= n m) (>= o p)))
  arith-elim-lt (=> true (= (< n m) (not (>= n m))))
  arith-elim-gt (=> true (= (> n m) (not (<= n m))))
  
  arith-norm-geq-false (=> (= (>= (arith_norm_term (- n m)) 0) false) (= (>= n m) false))
  arith-norm-leq-false (=> (= (<= (arith_norm_term (- n m)) 0) false) (= (<= n m) false))
  arith-norm-geq-true (=> true (= (>= n n) true))
  arith-norm-leq-true (=> true (= (<= n n) true))
  
  
  not-not-elim (=> true (= (not (not b)) b))
  and-flatten (=> (= (flatten_bool (and b c)) d) (= (and b c) d))
  or-flatten (=> (= (flatten_bool (and b c)) d) (= (or b c) d))
  iff-true (=> true (= (= b true) b))
  iff-false (=> true (= (= b false) (not b)))
  iff-true2 (=> true (= (= true b) b))
  iff-false2 (=> true (= (= false b) (not b)))
  
  ; re-loop-elim (exists ((r RegLen)) (re.loop r n m))
  ; re-loop-elim (re.loop r (const n) (const m)) ----> t[r]
  ;              (re.loop C (const n) (const m)) ----> t[C]  /  s
  ; plus-eval (+ (const n) (const m))
  ; plus-eval2 (=> (= (Rewriter::rewrite (+ (const n) (const m))) e) (= (+ (const n) (const m)) e))
))

; via-rewrite (=> (= (rewrite x) y) (= x y))
