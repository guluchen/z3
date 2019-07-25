(declare-fun status () String)


(assert (not ( not ( = ( str.len status  ) 3  )  )))


(check-sat)


(get-value (status))