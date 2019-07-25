(declare-fun word () String)
(declare-fun abbr () String)


(assert ( = ( + 0 0  ) ( str.len word  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))