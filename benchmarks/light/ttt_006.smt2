(declare-fun g () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)
(declare-fun e () String)
(declare-fun h () String)
(assert (= (str.++ g (str.++ "a" c)) (str.++ h (str.++ b "h"))))
(assert (= (str.++ "d" (str.++ a a)) (str.++ c (str.++ "b" e))))
(assert (= (str.++ "e" (str.++ d h)) (str.++ "d" (str.++ e d))))
(check-sat)
(get-model)