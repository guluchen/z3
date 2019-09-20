(declare-fun tstr () String)


(assert ( < ( - ( str.len tstr  ) 0  ) 2  ))


(check-sat)


(get-value (tstr))