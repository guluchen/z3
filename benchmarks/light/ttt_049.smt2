(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)
(declare-fun f () String)
(assert (= (str.++ "e" (str.++ "b" "a")) (str.++ f (str.++ "g" d))))
(assert (= (str.++ "h" (str.++ a "f")) (str.++ b (str.++ f b))))
(assert (= (str.++ "h" (str.++ "c" "c")) (str.++ "e" (str.++ "c" c))))
(check-sat)
(get-model)