(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace x (str.replace "A" "B" y) x) (str.replace x "A" x))))
(check-sat)
