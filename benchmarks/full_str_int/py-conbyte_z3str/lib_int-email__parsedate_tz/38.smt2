(declare-fun data () String)


(assert (not ( = 1 3  )))

(assert (not ( >= ( str.indexof data "," 0  ) 0  )))

(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "aae"  ) ( = "tue" "aae"  )  ) ( = "wed" "aae"  )  ) ( = "thu" "aae"  )  ) ( = "fri" "aae"  )  ) ( = "sat" "aae"  )  ) ( = "sun" "aae"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 1 4  ))


(check-sat)


(get-value (data))