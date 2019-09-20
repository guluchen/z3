(declare-fun data () String)


(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( or ( or ( or ( or ( or ( or ( = "mon" "/,)!!"  ) ( = "tue" "/,)!!"  )  ) ( = "wed" "/,)!!"  )  ) ( = "thu" "/,)!!"  )  ) ( = "fri" "/,)!!"  )  ) ( = "sat" "/,)!!"  )  ) ( = "sun" "/,)!!"  )  ))


(check-sat)


(get-value (data))