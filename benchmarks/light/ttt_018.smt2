(declare-fun g () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun e () String)
(declare-fun b () String)
(declare-fun f () String)
(assert (= (str.++ g (str.++ e "b")) (str.++ c (str.++ c "a"))))
(assert (= (str.++ b (str.++ "d" d)) (str.++ f (str.++ "g" f))))
(assert (= (str.++ d (str.++ "b" e)) (str.++ "g" (str.++ "a" "f"))))
(check-sat)
(get-model)