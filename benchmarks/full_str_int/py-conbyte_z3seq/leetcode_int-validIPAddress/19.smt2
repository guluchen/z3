(declare-fun IP () String)


(assert ( str.contains IP "."  ))
(assert (not ( not ( = 2 4  )  )))


(check-sat)


(get-value (IP))