(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun a () String)

(assert (not (not (= (ite (>= (+ (str.len a) (- 1)) 0) 1 0) 0))))

(check-sat)

(get-value (a))