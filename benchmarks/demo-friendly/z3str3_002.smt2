(declare-fun g () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun e () String)
(declare-fun h () String)
(declare-fun f () String)
(assert (= (str.++ f (str.++ c g)) (str.++ d (str.++ "a" h))))
(assert (= (str.++ "f" (str.++ "c" b)) (str.++ h (str.++ d "e"))))
(assert (= (str.++ "d" (str.++ "f" b)) (str.++ e (str.++ "e" "h"))))
(check-sat)
(get-model)