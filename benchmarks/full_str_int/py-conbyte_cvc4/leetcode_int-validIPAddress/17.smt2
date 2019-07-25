(declare-fun IP () String)


(assert ( str.contains IP "."  ))
(assert (not ( not ( = 3 4  )  )))


(check-sat)


(get-value (IP))