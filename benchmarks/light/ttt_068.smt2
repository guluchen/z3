(declare-fun f () String)
(declare-fun e () String)
(declare-fun b () String)
(declare-fun a () String)
(assert (= (str.++ b (str.++ "f" e)) (str.++ "a" (str.++ "g" "d"))))
(assert (= (str.++ "f" (str.++ "g" "a")) (str.++ a (str.++ f "b"))))
(assert (= (str.++ "g" (str.++ "b" a)) (str.++ "f" (str.++ "g" "a"))))
(check-sat)
(get-model)