(declare-fun x () String)
(declare-fun y () String)

(assert (= (str.++ x y) (str.++ "ab" x)))
(assert (= (str.len y) 2))

(check-sat)
(get-model)
