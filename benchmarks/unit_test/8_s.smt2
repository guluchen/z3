(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.suffixof "A" y) (str.prefixof "A" y))))
(check-sat)
