(declare-fun IP () String)


(assert (not ( str.contains IP "."  )))


(check-sat)


(get-value (IP))