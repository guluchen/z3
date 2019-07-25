(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))
(assert ( >= ( + 0 0  ) ( str.len word  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))