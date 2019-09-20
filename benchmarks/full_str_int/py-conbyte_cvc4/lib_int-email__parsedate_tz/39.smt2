(declare-fun data () String)


(assert (not ( = 1 3  )))

(assert ( >= ( str.indexof data "," 0  ) 0  ))

(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" ",a"  ) ( = "tue" ",a"  )  ) ( = "wed" ",a"  )  ) ( = "thu" ",a"  )  ) ( = "fri" ",a"  )  ) ( = "sat" ",a"  )  ) ( = "sun" ",a"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 1 4  ))


(check-sat)


(get-value (data))