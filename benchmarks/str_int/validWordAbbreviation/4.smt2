(declare-fun word () String)
(declare-fun abbr () String)


(assert ( < ( + 0 1  ) ( str.len abbr  )  ))

(assert (not ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  )))

(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < 0 ( str.len abbr  )  ))
(assert (not ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (word))
(get-value (abbr))