(declare-fun data () String)


(assert ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" "\x00\x00\x00"  ) ( = "feb" "\x00\x00\x00"  )  ) ( = "mar" "\x00\x00\x00"  )  ) ( = "apr" "\x00\x00\x00"  )  ) ( = "may" "\x00\x00\x00"  )  ) ( = "jun" "\x00\x00\x00"  )  ) ( = "jul" "\x00\x00\x00"  )  ) ( = "aug" "\x00\x00\x00"  )  ) ( = "sep" "\x00\x00\x00"  )  ) ( = "oct" "\x00\x00\x00"  )  ) ( = "nov" "\x00\x00\x00"  )  ) ( = "dec" "\x00\x00\x00"  )  ) ( = "january" "\x00\x00\x00"  )  ) ( = "february" "\x00\x00\x00"  )  ) ( = "march" "\x00\x00\x00"  )  ) ( = "april" "\x00\x00\x00"  )  ) ( = "may" "\x00\x00\x00"  )  ) ( = "june" "\x00\x00\x00"  )  ) ( = "july" "\x00\x00\x00"  )  ) ( = "august" "\x00\x00\x00"  )  ) ( = "september" "\x00\x00\x00"  )  ) ( = "october" "\x00\x00\x00"  )  ) ( = "november" "\x00\x00\x00"  )  ) ( = "december" "\x00\x00\x00"  )  )  ))

(assert (not ( < 5 5  )))

(assert (not ( = 5 4  )))

(assert (not ( = 5 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" "2"  ) ( = "feb" "2"  )  ) ( = "mar" "2"  )  ) ( = "apr" "2"  )  ) ( = "may" "2"  )  ) ( = "jun" "2"  )  ) ( = "jul" "2"  )  ) ( = "aug" "2"  )  ) ( = "sep" "2"  )  ) ( = "oct" "2"  )  ) ( = "nov" "2"  )  ) ( = "dec" "2"  )  ) ( = "january" "2"  )  ) ( = "february" "2"  )  ) ( = "march" "2"  )  ) ( = "april" "2"  )  ) ( = "may" "2"  )  ) ( = "june" "2"  )  ) ( = "july" "2"  )  ) ( = "august" "2"  )  ) ( = "september" "2"  )  ) ( = "october" "2"  )  ) ( = "november" "2"  )  ) ( = "december" "2"  )  )  )))


(check-sat)


(get-value (data))