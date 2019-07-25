(declare-fun s () String)


(assert (not ( > ( str.len s  ) 12  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert (not ( str.in.re s ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (s))