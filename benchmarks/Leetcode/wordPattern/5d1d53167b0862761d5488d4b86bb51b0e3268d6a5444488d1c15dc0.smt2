(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun str () String)
(declare-fun pattern () String)

(assert (and (and (and (not (not (not (= (ite (not (= str str)) 1 0) 0)))) (not (not (= (ite (not (= (str.len pattern) 1)) 1 0) 0)))) (not (not (= (ite (str.contains str " ") 1 0) 0)))) (not (not (= (ite (= (str.len str) 0) 1 0) 0)))))

(check-sat)

(get-value (str))
(get-value (pattern))