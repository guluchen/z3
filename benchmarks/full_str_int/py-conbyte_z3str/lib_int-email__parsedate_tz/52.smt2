(declare-fun data () String)


(assert (not ( = 1 3  )))

(assert (not ( >= ( str.indexof data "," 0  ) 0  )))

(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "au_"  ) ( = "tue" "au_"  )  ) ( = "wed" "au_"  )  ) ( = "thu" "au_"  )  ) ( = "fri" "au_"  )  ) ( = "sat" "au_"  )  ) ( = "sun" "au_"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 1 4  ))


(check-sat)


(get-value (data))