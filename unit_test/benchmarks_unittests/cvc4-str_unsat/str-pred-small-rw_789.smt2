(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.suffixof (str.replace "B" x "") x) (str.suffixof "B" x))))
(check-sat)
