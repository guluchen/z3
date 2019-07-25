(declare-fun data () String)


(assert (not ( = 2 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 2 4  ))


(check-sat)


(get-value (data))