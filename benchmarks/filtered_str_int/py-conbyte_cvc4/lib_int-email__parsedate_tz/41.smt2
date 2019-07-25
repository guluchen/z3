(declare-fun data () String)


(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" ",a"  ) ( = "tue" ",a"  )  ) ( = "wed" ",a"  )  ) ( = "thu" ",a"  )  ) ( = "fri" ",a"  )  ) ( = "sat" ",a"  )  ) ( = "sun" ",a"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( >= ( str.indexof data "," 0  ) 0  )))


(check-sat)


(get-value (data))