(declare-fun word () String)
(declare-fun abbr () String)


(assert ( < 0 ( str.len abbr  )  ))
(assert ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))