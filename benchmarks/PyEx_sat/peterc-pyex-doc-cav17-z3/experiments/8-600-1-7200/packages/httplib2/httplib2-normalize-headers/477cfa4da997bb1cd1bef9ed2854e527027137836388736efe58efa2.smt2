(set-logic QF_S) (declare-fun key1 () String)

(assert (and (not (not (not (= (ite (str.contains key1 "B") 1 0) 0)))) (not (not (= (ite (str.contains key1 "A") 1 0) 0)))))

(check-sat)

;(get-value (key1))