(declare-fun data () String)


(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( or ( or ( or ( or ( or ( or ( = "mon" "aae"  ) ( = "tue" "aae"  )  ) ( = "wed" "aae"  )  ) ( = "thu" "aae"  )  ) ( = "fri" "aae"  )  ) ( = "sat" "aae"  )  ) ( = "sun" "aae"  )  ))


(check-sat)


(get-value (data))