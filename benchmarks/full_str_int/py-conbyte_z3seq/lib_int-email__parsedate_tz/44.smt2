(declare-fun data () String)


(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 2 3  ))


(check-sat)


(get-value (data))