(declare-fun data () String)


(assert (not ( >= ( str.indexof data "," 0  ) 0  )))

(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "\x00"  ) ( = "tue" "\x00"  )  ) ( = "wed" "\x00"  )  ) ( = "thu" "\x00"  )  ) ( = "fri" "\x00"  )  ) ( = "sat" "\x00"  )  ) ( = "sun" "\x00"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( = 1 3  ))


(check-sat)


(get-value (data))