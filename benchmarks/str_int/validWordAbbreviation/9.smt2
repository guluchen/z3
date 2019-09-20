(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( < 0 ( str.len abbr  )  )))


(check-sat)


(get-value (word))
(get-value (abbr))