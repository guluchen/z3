(declare-fun num1 () String)
(declare-fun num2 () String)


(assert (not ( >= ( + ( - (- 1) 1  ) ( str.len "0"  )  ) 0  )))

(assert (not ( >= ( + ( - (- 1) 1  ) ( str.len "0"  )  ) 0  )))

(assert (not ( >= ( + ( - (- 1) 1  ) ( ite ( < ( str.len "0"  ) ( str.len "0"  )  ) ( str.len "0"  ) ( str.len "0"  )  )  ) 0  )))

(assert (not ( >= ( + ( + ( ite ( str.prefixof "-" ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  ) 1 ( - ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  )  ) ( ite ( str.prefixof "-" ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  ) 1 ( - ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  )  )  ) 0  ) 10  )))

(assert ( ite ( str.prefixof "-" ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  ) 1 ( - ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( ite ( str.prefixof "-" ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  ) 1 ( - ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at "0" ( + ( str.len "0"  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + (- 1) ( ite ( < ( str.len "0"  ) ( str.len "0"  )  ) ( str.len "0"  ) ( str.len "0"  )  )  ) 0  ))

(assert ( = ( str.len num2  ) 0  ))

(assert ( = ( str.len num1  ) 0  ))
(assert ( not ( = 0 0  )  ))


(check-sat)


(get-value (num1))
(get-value (num2))