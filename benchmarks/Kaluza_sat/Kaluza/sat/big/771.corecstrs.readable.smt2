(declare-fun M0_2 () String)
(declare-fun M0_8 () String)
(declare-fun M1_2 () String)
(declare-fun M2_2 () String)
(declare-fun M3_2 () String)
(declare-fun M4_2 () String)
(declare-fun M5_2 () String)
(declare-fun M6_2 () String)
(declare-fun M7_2 () String)
(declare-fun P0_2 () String)
(declare-fun P0_8 () String)
(declare-fun P1_2 () String)
(declare-fun P2_2 () String)
(declare-fun P3_2 () String)
(declare-fun P4_2 () String)
(declare-fun P5_2 () String)
(declare-fun P6_2 () String)
(declare-fun P7_2 () String)
(declare-fun PCTEMP_LHS_1 () String)
(declare-fun PCTEMP_LHS_1_idx_0 () String)
(declare-fun PCTEMP_LHS_1_idx_1 () String)
(declare-fun PCTEMP_LHS_1_idx_2 () String)
(declare-fun PCTEMP_LHS_1_idx_3 () String)
(declare-fun PCTEMP_LHS_1_idx_4 () String)
(declare-fun PCTEMP_LHS_1_idx_5 () String)
(declare-fun PCTEMP_LHS_1_idx_6 () String)
(declare-fun PCTEMP_LHS_1_idx_7 () String)
(declare-fun PCTEMP_LHS_1_idx_8 () String)
(declare-fun PCTEMP_LHS_2_idx_0 () String)
(declare-fun PCTEMP_LHS_2_idx_1 () String)
(declare-fun T0_2 () String)
(declare-fun T0_8 () String)
(declare-fun T1_2 () String)
(declare-fun T1_8 () String)
(declare-fun T2_2 () String)
(declare-fun T3_2 () String)
(declare-fun T4_2 () String)
(declare-fun T5_2 () String)
(declare-fun T6_2 () String)
(declare-fun T7_2 () String)
(declare-fun T8_2 () String)
(declare-fun T_2 () Int)
(declare-fun T_3 () Bool)
(declare-fun T_4 () String)
(declare-fun T_6 () String)
(declare-fun T_7 () Bool)
(declare-fun var_0xINPUT_180353 () String)
(assert (= T8_2 PCTEMP_LHS_1_idx_8))
(assert (= T0_2 var_0xINPUT_180353))
(assert (= M7_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_7 (str.to.re ";" ))))
(assert (= P7_2 (str.++ PCTEMP_LHS_1_idx_7 M7_2)))
(assert (= T7_2 (str.++ P7_2 T8_2)))
(assert (= M6_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_6 (str.to.re ";" ))))
(assert (= P6_2 (str.++ PCTEMP_LHS_1_idx_6 M6_2)))
(assert (= T6_2 (str.++ P6_2 T7_2)))
(assert (= M5_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_5 (str.to.re ";" ))))
(assert (= P5_2 (str.++ PCTEMP_LHS_1_idx_5 M5_2)))
(assert (= T5_2 (str.++ P5_2 T6_2)))
(assert (= M4_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_4 (str.to.re ";" ))))
(assert (= P4_2 (str.++ PCTEMP_LHS_1_idx_4 M4_2)))
(assert (= T4_2 (str.++ P4_2 T5_2)))
(assert (= M3_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_3 (str.to.re ";" ))))
(assert (= P3_2 (str.++ PCTEMP_LHS_1_idx_3 M3_2)))
(assert (= T3_2 (str.++ P3_2 T4_2)))
(assert (= M2_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_2 (str.to.re ";" ))))
(assert (= P2_2 (str.++ PCTEMP_LHS_1_idx_2 M2_2)))
(assert (= T2_2 (str.++ P2_2 T3_2)))
(assert (= M1_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_1 (str.to.re ";" ))))
(assert (= P1_2 (str.++ PCTEMP_LHS_1_idx_1 M1_2)))
(assert (= T1_2 (str.++ P1_2 T2_2)))
(assert (= M0_2 ";"))
(assert (not (str.in.re PCTEMP_LHS_1_idx_0 (str.to.re ";" ))))
(assert (= P0_2 (str.++ PCTEMP_LHS_1_idx_0 M0_2)))
(assert (= T0_2 (str.++ P0_2 T1_2)))
(assert (= T_2 (str.len PCTEMP_LHS_1)))
(assert (= T_3 (< 0 T_2)))
(assert T_3)
(assert (= T_4 PCTEMP_LHS_1_idx_0))
(assert (= T1_8 PCTEMP_LHS_2_idx_1))
(assert (= T0_8 T_4))
(assert (= M0_8 "="))
(assert (not (str.in.re PCTEMP_LHS_2_idx_0 (str.to.re "=" ))))
(assert (= P0_8 (str.++ PCTEMP_LHS_2_idx_0 M0_8)))
(assert (= T0_8 (str.++ P0_8 T1_8)))
(assert (= T_6 PCTEMP_LHS_2_idx_0))
(assert (= T_7 (= T_6 "BizographicData")))
(assert T_7)
(check-sat)
