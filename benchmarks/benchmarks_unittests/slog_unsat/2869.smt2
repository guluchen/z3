(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_4 () String)
(assert (= literal_4 "\x2f\x79\x6f\x75\x72\x2f\x70\x61\x74\x68\x2f\x74\x6f\x2f\x6e\x75\x63\x6c\x65\x75\x73\x2f\x6c\x69\x62\x73\x2f\x67\x6c\x6f\x62\x61\x6c\x66\x75\x6e\x63\x74\x69\x6f\x6e\x73\x2e\x70\x68\x70"))
(assert (str.in.re literal_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(check-sat)
(get-model)
