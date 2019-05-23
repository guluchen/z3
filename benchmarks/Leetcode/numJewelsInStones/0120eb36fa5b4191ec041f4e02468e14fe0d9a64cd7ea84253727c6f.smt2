(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun S () String)
(declare-fun J () String)

(assert (and (not (not (not (= (ite (= (str.len S) 0) 1 0) 0)))) (not (not (= (ite (= (str.len J) 0) 1 0) 0)))))

(check-sat)

(get-value (S))
(get-value (J))