(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < 0 ( str.len abbr  )  ))
(assert ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))