(declare-fun s () String)


(assert (not ( = ( str.len s  ) 0  )))
(assert ( > ( str.len s  ) 12  ))


(check-sat)


(get-value (s))