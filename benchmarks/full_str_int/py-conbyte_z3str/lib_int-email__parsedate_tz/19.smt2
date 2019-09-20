(declare-fun data () String)


(assert ( = ( str.len data  ) 0  ))


(check-sat)


(get-value (data))