(declare-fun num1 () String)
(declare-fun num2 () String)


(assert ( = ( str.len num1  ) 0  ))
(assert (not ( = ( str.len num2  ) 0  )))


(check-sat)


(get-value (num1))
(get-value (num2))