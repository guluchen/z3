(declare-fun data () String)


(assert (not ( = 0 4  )))

(assert (not ( = 0 3  )))

(assert ( str.suffixof "," data  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( < 0 5  )))


(check-sat)


(get-value (data))