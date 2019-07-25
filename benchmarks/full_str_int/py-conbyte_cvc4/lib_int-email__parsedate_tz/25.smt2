(declare-fun data () String)


(assert ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" ""  ) ( = "feb" ""  )  ) ( = "mar" ""  )  ) ( = "apr" ""  )  ) ( = "may" ""  )  ) ( = "jun" ""  )  ) ( = "jul" ""  )  ) ( = "aug" ""  )  ) ( = "sep" ""  )  ) ( = "oct" ""  )  ) ( = "nov" ""  )  ) ( = "dec" ""  )  ) ( = "january" ""  )  ) ( = "february" ""  )  ) ( = "march" ""  )  ) ( = "april" ""  )  ) ( = "may" ""  )  ) ( = "june" ""  )  ) ( = "july" ""  )  ) ( = "august" ""  )  ) ( = "september" ""  )  ) ( = "october" ""  )  ) ( = "november" ""  )  ) ( = "december" ""  )  )  ))

(assert (not ( < 5 5  )))

(assert (not ( = 5 4  )))

(assert (not ( = 5 3  )))

(assert ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  ))

(assert (not ( = ( str.len data  ) 0  )))
(assert (not ( not ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( or ( = "jan" ""  ) ( = "feb" ""  )  ) ( = "mar" ""  )  ) ( = "apr" ""  )  ) ( = "may" ""  )  ) ( = "jun" ""  )  ) ( = "jul" ""  )  ) ( = "aug" ""  )  ) ( = "sep" ""  )  ) ( = "oct" ""  )  ) ( = "nov" ""  )  ) ( = "dec" ""  )  ) ( = "january" ""  )  ) ( = "february" ""  )  ) ( = "march" ""  )  ) ( = "april" ""  )  ) ( = "may" ""  )  ) ( = "june" ""  )  ) ( = "july" ""  )  ) ( = "august" ""  )  ) ( = "september" ""  )  ) ( = "october" ""  )  ) ( = "november" ""  )  ) ( = "december" ""  )  )  )))


(check-sat)


(get-value (data))