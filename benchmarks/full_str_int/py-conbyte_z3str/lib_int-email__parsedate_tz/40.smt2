(declare-fun data () String)


(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "aae"  ) ( = "tue" "aae"  )  ) ( = "wed" "aae"  )  ) ( = "thu" "aae"  )  ) ( = "fri" "aae"  )  ) ( = "sat" "aae"  )  ) ( = "sun" "aae"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( >= ( str.indexof data "," 0  ) 0  ))


(check-sat)


(get-value (data))