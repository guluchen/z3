(declare-fun IP () String)


(assert ( str.contains IP "."  ))
(assert ( not ( = 4 4  )  ))


(check-sat)


(get-value (IP))