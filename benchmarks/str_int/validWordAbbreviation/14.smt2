(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( < 0 ( str.len abbr  )  )))
(assert (not ( = ( + 0 0  ) ( str.len word  )  )))


(check-sat)


(get-value (word))
(get-value (abbr))