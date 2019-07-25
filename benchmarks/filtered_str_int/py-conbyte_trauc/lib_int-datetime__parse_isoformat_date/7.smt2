(declare-fun dtstr () String)


(assert ( not ( = ( str.len dtstr  ) 10  )  ))


(check-sat)


(get-value (dtstr))