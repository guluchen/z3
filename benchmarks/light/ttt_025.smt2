(declare-fun d () String)
(declare-fun e () String)
(declare-fun c () String)
(declare-fun a () String)
(declare-fun f () String)
(assert (= (str.++ "f" (str.++ "f" d)) (str.++ f (str.++ d "d"))))
(assert (= (str.++ "d" (str.++ "c" "g")) (str.++ "b" (str.++ a "c"))))
(assert (= (str.++ e (str.++ c f)) (str.++ "h" (str.++ a c))))
(check-sat)
(get-model)