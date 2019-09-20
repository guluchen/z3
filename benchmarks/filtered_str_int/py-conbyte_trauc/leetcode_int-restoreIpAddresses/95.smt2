(declare-fun s () String)


(assert ( = ( str.len s  ) 0  ))


(check-sat)


(get-value (s))