(set-logic QF_S) (declare-fun url () String)

(assert (not (not (= (ite (= url url) 1 0) 0))))

(check-sat)

;(get-value (url))