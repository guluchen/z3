(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun s () String)
(declare-fun t () String)

(assert (not (not (not (= (ite (not (= (str.len s) (str.len t))) 1 0) 0)))))

(check-sat)

(get-value (s))
(get-value (t))