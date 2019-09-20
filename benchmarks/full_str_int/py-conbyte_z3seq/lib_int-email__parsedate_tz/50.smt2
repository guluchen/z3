(declare-fun data () String)


(assert (not ( = ( str.len data  ) 0  )))
(assert ( str.suffixof "," data  ))


(check-sat)


(get-value (data))