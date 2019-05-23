(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun s () String)
(declare-fun in0 () String)

(assert (not (not (= (ite (<= (+ (- (str.len s) (* (str.len in0) 2)) 1) 0) 1 0) 0))))

(check-sat)

(get-value (s))
(get-value (in0))