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
(declare-fun var_0xINPUT_85216 () String)
(assert (= T_1 (not (= "AA1ND6MEXd" var_0xINPUT_85216))))
(assert (= T_2 (not T_1)))
(assert T_2)
(assert (= T_3 (not (= "" var_0xINPUT_85216))))
(assert T_3)
(assert (= T_4 (= var_0xINPUT_85216 "Example:")))
(assert (= T_5 (not T_4)))
(assert T_5)
(assert (= T_6 (not (= "" var_0xINPUT_85216))))
(assert T_6)
(assert (= T_7 (= var_0xINPUT_85216 "Example:")))
(assert (= T_8 (not T_7)))
(assert T_8)
(assert (= T_9 (not (= var_0xINPUT_85216 "AA1ND6MEXd"))))
(assert (= T_a (not T_9)))
(assert T_a)
(check-sat)
