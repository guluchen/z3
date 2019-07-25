(declare-fun IP () String)


(assert (not ( str.contains IP "."  )))
(assert (not ( not ( = 1 8  )  )))


(check-sat)


(get-value (IP))