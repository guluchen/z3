(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun pattern () String)
(declare-fun str () String)

(assert (and (not (not (= (ite (not (= (str.len pattern) 1)) 1 0) 0))) (not (= (ite (= (str.len str) 0) 1 0) 0))))

(check-sat)

(get-value (pattern))
(get-value (str))