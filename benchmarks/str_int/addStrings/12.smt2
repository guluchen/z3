(declare-fun num1 () String)
(declare-fun num2 () String)


(assert (not ( <= ( ite ( str.prefixof "-" num1  ) ( - ( str.to.int ( str.substr num1 1 ( - ( str.len num1  ) 1  )  )  )  ) ( str.to.int num1  )  ) 0  )))

(assert ( ite ( str.prefixof "-" num1  ) ( ite ( = (- 1) ( str.to.int ( str.substr num1 1 ( - ( str.len num1  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int num1  )  ) false true  )  ))

(assert (not ( = ( str.len num1  ) 0  )))
(assert ( = ( str.len num2  ) 0  ))


(check-sat)


(get-value (num1))
(get-value (num2))