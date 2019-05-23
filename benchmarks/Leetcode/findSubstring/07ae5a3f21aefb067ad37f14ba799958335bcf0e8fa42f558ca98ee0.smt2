(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun in0 () String)
(declare-fun in1 () String)

(assert (not (not (= (ite (= in0 in1) 1 0) 0))))

(check-sat)

(get-value (in0))
(get-value (in1))