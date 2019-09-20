(declare-fun num1 () String)
(declare-fun num2 () String)


(assert ( = ( str.len num2  ) 0  ))

(assert ( = ( str.len num1  ) 0  ))
(assert (not ( >= ( + (- 1) ( ite ( < ( str.len "0"  ) ( str.len "0"  )  ) ( str.len "0"  ) ( str.len "0"  )  )  ) 0  )))


(check-sat)


(get-value (num1))
(get-value (num2))