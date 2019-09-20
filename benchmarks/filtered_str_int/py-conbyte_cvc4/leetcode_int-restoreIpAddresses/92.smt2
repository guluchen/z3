(declare-fun s () String)


(assert ( str.in.re s ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( > ( str.len s  ) 12  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 0  )))


(check-sat)


(get-value (s))