(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.replace x "" (str.replace "A" "" y)) (str.replace x "" (str.++ y "A")))))
(check-sat)
