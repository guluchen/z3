(declare-fun data () String)


(assert ( str.suffixof "," data  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 0 3  ))


(check-sat)


(get-value (data))