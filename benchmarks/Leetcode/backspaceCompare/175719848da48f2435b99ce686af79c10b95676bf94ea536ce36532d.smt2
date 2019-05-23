(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun S () String)
(declare-fun T () String)

(assert (not (not (= (ite (= S T) 1 0) 0))))

(check-sat)

(get-value (S))
(get-value (T))