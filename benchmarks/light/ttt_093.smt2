(declare-fun d () String)
(declare-fun e () String)
(declare-fun c () String)
(declare-fun a () String)
(declare-fun h () String)
(declare-fun f () String)
(assert (= (str.++ h (str.++ "a" e)) (str.++ c (str.++ d h))))
(assert (= (str.++ f (str.++ "b" "f")) (str.++ "f" (str.++ c "c"))))
(assert (= (str.++ f (str.++ "f" e)) (str.++ a (str.++ "a" "e"))))
(check-sat)
(get-model)