(declare-fun data () String)


(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  )))


(check-sat)


(get-value (data))