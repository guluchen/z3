(declare-fun data () String)


(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "au_"  ) ( = "tue" "au_"  )  ) ( = "wed" "au_"  )  ) ( = "thu" "au_"  )  ) ( = "fri" "au_"  )  ) ( = "sat" "au_"  )  ) ( = "sun" "au_"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( >= ( str.indexof data "," 0  ) 0  ))


(check-sat)


(get-value (data))