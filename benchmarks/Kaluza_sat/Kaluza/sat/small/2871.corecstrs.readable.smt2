(declare-fun T_1 () Bool)
(declare-fun T_2 () Bool)
(declare-fun T_3 () Bool)
(declare-fun T_4 () Bool)
(declare-fun T_5 () Bool)
(declare-fun T_6 () Bool)
(declare-fun T_7 () Bool)
(declare-fun T_8 () Bool)
(declare-fun T_9 () Bool)
(declare-fun T_a () Bool)
(declare-fun var_0xINPUT_243357 () String)
(assert (= T_1 (not (= "" var_0xINPUT_243357))))
(assert T_1)
(assert (= T_2 (not (= "" var_0xINPUT_243357))))
(assert T_2)
(assert (= T_3 (not (= var_0xINPUT_243357 ""))))
(assert T_3)
(assert (= T_4 (not (= "" var_0xINPUT_243357))))
(assert T_4)
(assert (= T_5 (= var_0xINPUT_243357 "")))
(assert (= T_6 (not T_5)))
(assert T_6)
(assert (= T_7 (not (= "" var_0xINPUT_243357))))
(assert T_7)
(assert (= T_8 (= var_0xINPUT_243357 "Example:")))
(assert (= T_9 (not T_8)))
(assert T_9)
(assert (= T_a (not (= var_0xINPUT_243357 "2vbcJ9lN6J"))))
(assert T_a)
(check-sat)
