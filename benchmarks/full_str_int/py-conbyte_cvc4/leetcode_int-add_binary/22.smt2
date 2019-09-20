(declare-fun a () String)
(declare-fun b () String)


(assert (not ( >= ( + ( str.len a  ) (- 1)  ) 0  )))
(assert (str.in.re a (re.+ (re.range "0" "1"))))
(assert (str.in.re b (re.+ (re.range "0" "1"))))


(check-sat)


(get-value (a))
(get-value (b))