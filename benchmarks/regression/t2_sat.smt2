;(set-logic ALL_SUPPORTED)
;(set-option :strings-exp true)
;(set-option :produce-models true)
;(set-option :rewrite-divk true)

(declare-fun uri () String)

(assert (not (= (ite (str.contains (str.substr uri 10 (- (str.len uri) 10)) ".sock") 1 0) 0)))
(assert (not (= (ite (not (= (str.len (str.substr uri 10 (- (str.len uri) 10))) 0)) 1 0) 0)))
(assert (not (= (ite (str.prefixof "mongodb://" uri) 1 0) 0)))

(check-sat)

;(get-value (uri))
