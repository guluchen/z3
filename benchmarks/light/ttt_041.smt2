(declare-fun g () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)
(declare-fun f () String)
(assert (= (str.++ b (str.++ c g)) (str.++ f (str.++ "b" a))))
(assert (= (str.++ "h" (str.++ "c" "h")) (str.++ d (str.++ "h" a))))
(assert (= (str.++ "h" (str.++ f "a")) (str.++ g (str.++ "f" b))))
(check-sat)
(get-model)