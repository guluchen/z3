(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun s () String)
(declare-fun p () String)

(assert (not (not (= (ite (= s p) 1 0) 0))))

(check-sat)

(get-value (s))
(get-value (p))