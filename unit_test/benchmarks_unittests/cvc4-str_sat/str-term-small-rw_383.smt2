(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.substr (str.replace "" x y) z z) (str.substr y 1 (str.indexof "A" x z)))))
(check-sat)
