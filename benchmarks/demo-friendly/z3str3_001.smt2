(declare-const x String)
(declare-const y String)

(assert (= (str.++ y x) (str.++ "abc" y)))
(assert (= (str.len y) 100))

(check-sat)
(get-model)
