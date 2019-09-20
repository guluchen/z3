(declare-fun data () String)


(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( or ( or ( or ( or ( or ( or ( = "mon" "a"  ) ( = "tue" "a"  )  ) ( = "wed" "a"  )  ) ( = "thu" "a"  )  ) ( = "fri" "a"  )  ) ( = "sat" "a"  )  ) ( = "sun" "a"  )  ))


(check-sat)


(get-value (data))