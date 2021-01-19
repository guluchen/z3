(set-logic ALL)
(declare-const label String)
(declare-const a String)
(declare-const b String)
(declare-const bi Int)

(assert (= a (str.++ label ".cccc"))) ; a = label + ".copy"
(assert (= bi (str.indexof a "." 0))) ;
(assert (= b (str.substr a (+ bi 1) (str.len a)))) ;
(assert (= (str.indexof b "." 0) (- 1))) ;
(assert (not (str.prefixof "cccc" b))) ;
;(assert (= b "copy"));

(check-sat)

