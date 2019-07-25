(declare-fun s () String)


(assert (not ( = ( str.len s  ) 0  )))
(assert ( >= 0 1  ))


(check-sat)


(get-value (s))