(declare-fun data () String)


(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( or ( or ( or ( or ( or ( or ( = "mon" "ap,aaam,aed"  ) ( = "tue" "ap,aaam,aed"  )  ) ( = "wed" "ap,aaam,aed"  )  ) ( = "thu" "ap,aaam,aed"  )  ) ( = "fri" "ap,aaam,aed"  )  ) ( = "sat" "ap,aaam,aed"  )  ) ( = "sun" "ap,aaam,aed"  )  ))


(check-sat)


(get-value (data))