(declare-fun arg1 () String)
(declare-fun arg2 () String)


(assert (not ( = ( str.len arg2  ) 0  )))

(assert (not ( = ( str.len arg1  ) 0  )))
(assert ( < ( str.indexof arg1 ":" 0  ) 0  ))


(check-sat)


(get-value (arg1))
(get-value (arg2))