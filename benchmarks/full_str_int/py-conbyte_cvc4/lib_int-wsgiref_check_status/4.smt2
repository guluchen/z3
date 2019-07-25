(declare-fun status () String)


(assert (not ( not ( = ( str.len ""  ) 3  )  )))


(check-sat)


(get-value (status))