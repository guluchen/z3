(declare-fun data () String)


(assert (not ( < 5 5  )))

(assert (not ( > ( str.indexof "" "-" 0  ) 0  )))

(assert ( = ( str.indexof "" "+" 0  ) (- 1)  ))

(assert ( = 4 4  ))

(assert (not ( = 4 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" "\x00"  ) ( = "feb" "\x00"  )  ) ( = "mar" "\x00"  )  ) ( = "apr" "\x00"  )  ) ( = "may" "\x00"  )  ) ( = "jun" "\x00"  )  ) ( = "jul" "\x00"  )  ) ( = "aug" "\x00"  )  ) ( = "sep" "\x00"  )  ) ( = "oct" "\x00"  )  ) ( = "nov" "\x00"  )  ) ( = "dec" "\x00"  )  ) ( = "january" "\x00"  )  ) ( = "february" "\x00"  )  ) ( = "march" "\x00"  )  ) ( = "april" "\x00"  )  ) ( = "may" "\x00"  )  ) ( = "june" "\x00"  )  ) ( = "july" "\x00"  )  ) ( = "august" "\x00"  )  ) ( = "september" "\x00"  )  ) ( = "october" "\x00"  )  ) ( = "november" "\x00"  )  ) ( = "december" "\x00"  )  )  )))


(check-sat)


(get-value (data))