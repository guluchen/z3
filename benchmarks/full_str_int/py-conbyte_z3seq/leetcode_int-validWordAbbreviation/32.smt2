(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( str.in.re ( str.at abbr 3  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 2  ) ( str.at abbr 2  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 2  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 1  ) ( str.at abbr 1  )  )  )))

(assert (not ( >= ( + ( + ( + 0 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  )))

(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))
(assert ( >= ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))