(declare-fun x () String)
(declare-fun y () String)

(assert (= (str.++ x "a" y) (str.++ y "a" x)))
(assert (= (+ 9 (str.len y)) (str.len x)))
(assert (> (str.len y) 0))

(check-sat)
(get-model)
