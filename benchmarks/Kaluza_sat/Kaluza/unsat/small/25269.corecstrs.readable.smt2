(declare-fun I0_5 () Int)
(declare-fun PCTEMP_LHS_1 () Int)
(declare-fun T0_5 () String)
(declare-fun T1_5 () String)
(declare-fun T2_5 () String)
(declare-fun T3_5 () String)
(declare-fun T4_5 () String)
(declare-fun T5_5 () String)
(declare-fun T_1 () Bool)
(declare-fun T_2 () Bool)
(declare-fun T_3 () Bool)
(declare-fun T_5 () Bool)
(declare-fun T_6 () Bool)
(declare-fun T_SELECT_1 () Bool)
(declare-fun var_0xINPUT_48915 () String)
(assert (= T_1 (= "-" var_0xINPUT_48915)))
(assert (= T_2 (not T_1)))
(assert T_2)
(assert (= T_3 (= "" var_0xINPUT_48915)))
(assert T_3)
(assert (= T_SELECT_1 (not (= PCTEMP_LHS_1 (- 1)))))
(assert (ite T_SELECT_1 (and (= PCTEMP_LHS_1 (+ I0_5 0))(= var_0xINPUT_48915 (str.++ T0_5 T1_5))(= I0_5 (str.len T4_5))(= 0 (str.len T0_5))(= T1_5 (str.++ T2_5 T3_5))(= T2_5 (str.++ T4_5 T5_5))(= T5_5 "GASO=")(not (str.in.re T4_5 (re.++   (str.to.re "G" )  (re.++   (str.to.re "A" ) (re.++  (str.to.re "S" ) (re.++  (str.to.re "O" )  (str.to.re "=" )  ) ) ) ) ))) (and (= PCTEMP_LHS_1 (- 1))(= var_0xINPUT_48915 (str.++ T0_5 T1_5))(= 0 (str.len T0_5))(not (str.in.re T1_5 (re.++   (str.to.re "G" )  (re.++   (str.to.re "A" ) (re.++  (str.to.re "S" ) (re.++  (str.to.re "O" )  (str.to.re "=" )  ) ) ) ) )))))
(assert (= T_5 (< (- 1) PCTEMP_LHS_1)))
(assert (= T_6 (not T_5)))
(assert T_6)
(check-sat)
