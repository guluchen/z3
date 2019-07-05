(declare-fun s () String)

(assert ( = ( str.len s  ) 0  ))(assert (str.in.re s (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (s))