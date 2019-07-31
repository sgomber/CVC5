(declare-fun flatten_string (String) String)
(declare-fun sort_bool (Bool) Bool)
(declare-fun flatten_regexp (RegLan) RegLan)
(declare-fun sort_regexp (RegLan) RegLan)
(declare-fun arith_norm_term (Int) Int)
(declare-fun arith_norm_term_abs (Int) Int)
(proof-db (
  (x String) (y String) (z String) (w String) (v String)
  (n Int) (m Int) (o Int) (p Int) 
  (r RegLan) (s RegLan) (t RegLan)
  (b Bool) (c Bool) (d Bool)
) (
  ; general form needed since rewriter takes "shortcuts" like (str.len (str.++ x "A")) ---> (+ (str.len x) 1)
  len-concat-gen (=> (and (= (str.len x) n) (= (str.len y) m)) (= (str.len (str.++ x y)) (+ n m)))
  
  len-repl-inv (=> (= (= (str.len y) (str.len z)) true) (= (str.len (str.replace x y z)) (str.len x)))
  
  prefixof-elim (=> true (= (str.prefixof x y) (= x (str.substr y 0 (str.len x)))))
  suffixof-elim (=> true (= (str.suffixof x y) (= x (str.substr y (- (str.len y) (str.len x)) (str.len x)))))
  str.at-elim (=> true (= (str.at x n) (str.substr x n 1)))
  
  re-in-const-str (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  re-all-char (=> true (= (str.in.re x (re.* re.allchar)) true))
  re-concat-nctn (=> (>= (str.len y) (+ (str.len x) 1)) (= (str.in.re x (re.++ (str.to.re y) s)) false))
  
  ; recursion builtin
  re-union-elim (=> (= (str.in.re x s) b) (= (str.in.re x (re.union r s)) (or (str.in.re x r) b)))
  re-inter-elim (=> (= (str.in.re x s) b) (= (str.in.re x (re.inter r s)) (and (str.in.re x r) b)))
  
  re-concat-find-sing (=> (and (str.in.re x r) (str.in.re "" s)) (= (str.in.re x (re.++ r s)) true))
  re-concat-skip-sing (=> (and (str.in.re "" r) (str.in.re x s)) (= (str.in.re x (re.++ r s)) true))
  re-concat (=> (and (str.in.re x r) (str.in.re y s)) (= (str.in.re (str.++ x y) (re.++ r s)) true))
  re-consume (=> (= (str.in.re y (re.++ (str.to.re z) r)) b) (= (str.in.re (str.++ x y) (re.++ (str.to.re (str.++ x z)) r)) b))
  re-consume-sing (=> (= (str.in.re y r) b) (= (str.in.re (str.++ x y) (re.++ (str.to.re x) r)) b))
  re-consume-sing-sing (=> (= (str.in.re "" r) b) (= (str.in.re x (re.++ (str.to.re x) r)) b))

  ; annoyingly necessary due to representation of string constants
  re-consume-nested (=> (= (str.in.re (str.++ y z) (re.++ (str.to.re w) r)) b) (= (str.in.re (str.++ (str.++ x y) z) (re.++ (str.to.re (str.++ x w)) r)) b))
  re-consume-nested-sing (=> (= (str.in.re (str.++ y z) r) b) (= (str.in.re (str.++ (str.++ x y) z) (re.++ (str.to.re x) r)) b))
  
  ; needs recursion
  ;re-consume-match (=> (= (flatten_string x) (str.++ y w)) (= (str.in.re x (re.++ (str.to.re (str.++ y z)) r)) (str.in.re w (re.++ (str.to.re z) r))))
  ;re-consume-match (=> 
  ; (and (= (flatten_string x) (str.++ y w)) (= (str.in.re w (re.++ (str.to.re z) r)) b))
  ; (= (str.in.re x (re.++ (str.to.re (str.++ y z)) r)) b))
  
  re-clash (=> (and (= (= (str.len x) (str.len y)) true) (= (= x y) false)) (= (str.in.re (str.++ x z) (re.++ (str.to.re (str.++ y w)) r)) false))
  re-clash-nested (=> (and (= (= (str.len x) (str.len w)) true) (= (= x w) false)) (= (str.in.re (str.++ (str.++ x y) z) (re.++ (str.to.re (str.++ w v)) r)) false))
  
  re-str-to-re-true (=> true (= (str.in.re x (str.to.re x)) true))
  re-str-to-re-eq (=> true (= (str.in.re x (str.to.re y)) (= x y)))
  
  re-union1 (=> (str.in.re x r) (= (str.in.re x (re.union r s)) true))
  re-union2 (=> (str.in.re x s) (= (str.in.re x (re.union r s)) true))
  re-inter1 (=> (not (str.in.re x r)) (= (str.in.re x (re.inter r s)) false))
  re-inter2 (=> (not (str.in.re x s)) (= (str.in.re x (re.inter r s)) false))
  re-emp-in-star (=> true (= (str.in.re "" (re.* r)) true))
  
  re-concat-nostr (=> true (= (re.++ r re.nostr) re.nostr))
  re-concat-nostr2 (=> true (= (re.++ re.nostr r) re.nostr))
  re-star-nostr (=> true (= (re.* re.nostr) (str.to.re "")))
  
  re-concat-flatten (=> (= (flatten_regexp (re.++ r s)) t) (= (re.++ r s) t))
  
  re-all-char-elim (=> true (= (str.in.re x re.allchar) (= 1 (str.len x))))
  re-all-char (=> (= (= 1 (str.len x)) true) (= (str.in.re x re.allchar) true))
  
  re-to-ctn (=> true (= (str.in.re x (re.++ (re.* re.allchar) (str.to.re y) (re.* re.allchar))) (str.contains x y)))
  
  re-star-emp (=> true (= (re.* (str.to.re "")) (str.to.re "")))
  re-union-sort (=> (= (sort_regexp (re.union r s)) (sort_regexp t)) (= (re.union r s) t))
  re-inter-sort (=> (= (sort_regexp (re.inter r s)) (sort_regexp t)) (= (re.inter r s) t))
  re-union-all1 (=> (= r (re.* re.allchar)) (= (re.union r s) (re.* re.allchar)))
  re-union-all2 (=> (= s (re.* re.allchar)) (= (re.union r s) (re.* re.allchar)))
  re-inter-emp1 (=> (= r (re.* re.allchar)) (= (re.inter r s) (re.* re.allchar)))
  re-inter-emp2 (=> (= s (re.* re.allchar)) (= (re.inter r s) (re.* re.allchar)))
  
  concat-flatten (=> (= (flatten_string (str.++ x y)) (flatten_string z)) (= (str.++ x y) z))
  
  repl-id (=> true (= (str.replace x x y) y))
  repl-idem (=> true (= (str.replace x y y) x))
  repl-no (=> (= (str.contains x y) false) (= (str.replace x y z) x))
  repl-empty (=> true (= (str.replace x "" y) (str.++ y x)))
  repl-empty-inv (=> true (= (str.replace "" x "") ""))
  
  substr-emp (=> true (= (str.substr "" n m) ""))
  substr-id (=> (>= n (str.len x)) (= (str.substr x 0 n) x))
  substr-neg (=> (= (>= 0 (+ n 1)) true) (= (str.substr x n m) ""))
  substr-range (=> (>= 0 m) (= (str.substr x n m) ""))
  substr-oob (=> (= (>= n (str.len x)) true) (= (str.substr x n m) ""))
  
  substr-concat-len-ctn (=> (and (>= (str.len x) (+ n m)) (= (str.substr x n m) z)) (= (str.substr (str.++ x y) n m) z))
  substr-concat-len-nctn (=> (and (= (>= n (str.len x)) true) (= (- n (str.len x)) o)) (= (str.substr (str.++ x y) n m) (str.substr y o m)))
  substr-concat-len-in (=> (and (>= (- n (str.len x)) 0) (= (str.substr x 0 (- n (str.len x))) z)) (= (str.substr (str.++ x y) 0 n) (str.++ x z)))
  
  ctn-clash (=> (and (= (= (str.len x) (str.len y)) true) (= (= x y) false)) (= (str.contains x (str.++ y z)) false))
  ctn-concat-f1 (=> (= (str.contains x y) false) (= (str.contains x (str.++ y z)) false))
  ctn-concat-f2 (=> (= (str.contains x z) false) (= (str.contains x (str.++ y z)) false))
  ctn-concat-t1 (=> (= (str.contains x z) true) (= (str.contains (str.++ x y) z) true))
  ctn-concat-t2 (=> (= (str.contains y z) true) (= (str.contains (str.++ x y) z) true))
  ctn-id (=> true (= (str.contains x x) true))
  
  ctn-repl-emp (=> (not (str.contains y z)) (= (str.contains (str.replace "" x y) z) false))
  
  
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
  
  
  stoi-concat-ndigit1 (=> (= (str.to.int x) (- 1)) (= (str.to.int (str.++ x y)) (- 1)))
  stoi-concat-ndigit2 (=> (= (str.to.int y) (- 1)) (= (str.to.int (str.++ x y)) (- 1)))
  
  
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
  and-sort (=> (= (sort_bool (and b c)) (sort_bool d)) (= (and b c) d))
  and-false1 (=> (= b false) (= (and b c) false))
  and-false2 (=> (= c false) (= (and b c) false))
  or-sort (=> (= (sort_bool (or b c)) (sort_bool d)) (= (or b c) d))
  or-true1 (=> b (= (or b c) true))
  or-true2 (=> c (= (or b c) true))
  iff-true (=> true (= (= b true) b))
  iff-false (=> true (= (= b false) (not b)))
  iff-true2 (=> true (= (= true b) b))
  iff-false2 (=> true (= (= false b) (not b)))
  
  ite-true (=> true (= (ite true b c) b))
  ite-false (=> true (= (ite false b c) c))
  
  
  ; re-loop-elim (exists ((r RegLen)) (re.loop r n m))
  ; re-loop-elim (re.loop r (const n) (const m)) ----> t[r]
  ;              (re.loop C (const n) (const m)) ----> t[C]  /  s
  ; plus-eval (+ (const n) (const m))
  ; plus-eval2 (=> (= (Rewriter::rewrite (+ (const n) (const m))) e) (= (+ (const n) (const m)) e))
))

; via-rewrite (=> (= (rewrite x) y) (= x y))
