(declare-fun data () String)


(assert (not ( = 0 3  )))

(assert ( str.suffixof "," data  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 0 4  ))


(check-sat)


(get-value (data))