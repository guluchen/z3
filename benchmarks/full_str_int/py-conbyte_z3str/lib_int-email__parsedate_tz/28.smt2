(declare-fun data () String)


(assert (not ( = 1 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 1 4  ))


(check-sat)


(get-value (data))