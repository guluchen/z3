(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_2 () String)
(assert (= literal_2 "\x2f\x6d\x6f\x64\x2f\x2f\x6c\x69\x62\x2e\x70\x68\x70"))
(assert (str.in.re literal_2 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(check-sat)
(get-model)
