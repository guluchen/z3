(declare-fun data () String)


(assert ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" ""  ) ( = "feb" ""  )  ) ( = "mar" ""  )  ) ( = "apr" ""  )  ) ( = "may" ""  )  ) ( = "jun" ""  )  ) ( = "jul" ""  )  ) ( = "aug" ""  )  ) ( = "sep" ""  )  ) ( = "oct" ""  )  ) ( = "nov" ""  )  ) ( = "dec" ""  )  ) ( = "january" ""  )  ) ( = "february" ""  )  ) ( = "march" ""  )  ) ( = "april" ""  )  ) ( = "may" ""  )  ) ( = "june" ""  )  ) ( = "july" ""  )  ) ( = "august" ""  )  ) ( = "september" ""  )  ) ( = "october" ""  )  ) ( = "november" ""  )  ) ( = "december" ""  )  )  ))

(assert (not ( < 5 5  )))

(assert (not ( = 5 4  )))

(assert (not ( = 5 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" "4"  ) ( = "feb" "4"  )  ) ( = "mar" "4"  )  ) ( = "apr" "4"  )  ) ( = "may" "4"  )  ) ( = "jun" "4"  )  ) ( = "jul" "4"  )  ) ( = "aug" "4"  )  ) ( = "sep" "4"  )  ) ( = "oct" "4"  )  ) ( = "nov" "4"  )  ) ( = "dec" "4"  )  ) ( = "january" "4"  )  ) ( = "february" "4"  )  ) ( = "march" "4"  )  ) ( = "april" "4"  )  ) ( = "may" "4"  )  ) ( = "june" "4"  )  ) ( = "july" "4"  )  ) ( = "august" "4"  )  ) ( = "september" "4"  )  ) ( = "october" "4"  )  ) ( = "november" "4"  )  ) ( = "december" "4"  )  )  )))


(check-sat)


(get-value (data))