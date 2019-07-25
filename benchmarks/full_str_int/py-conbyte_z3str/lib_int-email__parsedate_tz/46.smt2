(declare-fun data () String)


(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "ap,aaam,aed"  ) ( = "tue" "ap,aaam,aed"  )  ) ( = "wed" "ap,aaam,aed"  )  ) ( = "thu" "ap,aaam,aed"  )  ) ( = "fri" "ap,aaam,aed"  )  ) ( = "sat" "ap,aaam,aed"  )  ) ( = "sun" "ap,aaam,aed"  )  )))

(assert (not ( str.suffixof "," data  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( >= ( str.indexof data "," 0  ) 0  )))


(check-sat)


(get-value (data))