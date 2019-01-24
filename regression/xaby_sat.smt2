(declare-fun T_1 () Bool)
(declare-fun x () String)
(declare-fun y () String)
(assert (=  (str.len x) 154))
(assert (=  (str.len y) 160))
(assert (= (str.++ y "ab" x) (str.++ x "ab" y) ))

(check-sat)
