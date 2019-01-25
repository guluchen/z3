(declare-fun T_1 () Bool)
(declare-fun x () String)
(declare-fun y () String)

(assert (= (str.len x) 155))
(assert (= (str.len y) 161))
(assert (= (str.++ y "ab" x) (str.++ x "ab" y)))

(check-sat)
