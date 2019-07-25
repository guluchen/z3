(declare-fun data () String)


(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( or ( or ( or ( or ( or ( or ( = "mon" "\x00"  ) ( = "tue" "\x00"  )  ) ( = "wed" "\x00"  )  ) ( = "thu" "\x00"  )  ) ( = "fri" "\x00"  )  ) ( = "sat" "\x00"  )  ) ( = "sun" "\x00"  )  ))


(check-sat)


(get-value (data))