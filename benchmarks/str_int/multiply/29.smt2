(declare-fun num1 () String)
(declare-fun num2 () String)

(assert (not ( = num1 "0"  )))
(assert ( = num2 "0"  ))(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))