(declare-fun num1 () String)
(declare-fun num2 () String)


(assert (not ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  )))

(assert (not ( >= ( + ( + ( ite ( str.prefixof "-" ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( - ( str.to.int ( str.substr ( str.at num1 ( + ( str.len num1  ) (- 2)  )  ) 1 ( - ( str.len ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  )  ) ( ite ( str.prefixof "-" ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  ) ( - ( str.to.int ( str.substr ( str.at num2 ( + ( str.len num2  ) (- 2)  )  ) 1 ( - ( str.len ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  )  ) 1  ) 10  )))

(assert ( ite ( str.prefixof "-" ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at num2 ( + ( str.len num2  ) (- 2)  )  ) 1 ( - ( str.len ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) false true  )  ))

(assert ( ite ( str.prefixof "-" ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at num1 ( + ( str.len num1  ) (- 2)  )  ) 1 ( - ( str.len ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( - (- 1) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))

(assert ( >= ( + ( + ( ite ( str.prefixof "-" ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at num1 ( + ( str.len num1  ) (- 1)  )  ) 1 ( - ( str.len ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  )  ) ( ite ( str.prefixof "-" ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at num2 ( + ( str.len num2  ) (- 1)  )  ) 1 ( - ( str.len ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  )  ) 0  ) 10  ))

(assert ( ite ( str.prefixof "-" ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at num2 ( + ( str.len num2  ) (- 1)  )  ) 1 ( - ( str.len ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( ite ( str.prefixof "-" ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at num1 ( + ( str.len num1  ) (- 1)  )  ) 1 ( - ( str.len ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + (- 1) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))

(assert (not ( <= ( ite ( str.prefixof "-" num2  ) ( - ( str.to.int ( str.substr num2 1 ( - ( str.len num2  ) 1  )  )  )  ) ( str.to.int num2  )  ) 0  )))

(assert ( ite ( str.prefixof "-" num2  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr num2 1 ( - ( str.len num2  ) 1  )  )  )  ) false true  ) ( > ( str.len num2  ) 1  )  ) ( ite ( = (- 1) ( str.to.int num2  )  ) false true  )  ))

(assert (not ( = ( str.len num2  ) 0  )))

(assert (not ( <= ( ite ( str.prefixof "-" num1  ) ( - ( str.to.int ( str.substr num1 1 ( - ( str.len num1  ) 1  )  )  )  ) ( str.to.int num1  )  ) 0  )))

(assert ( ite ( str.prefixof "-" num1  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr num1 1 ( - ( str.len num1  ) 1  )  )  )  ) false true  ) ( > ( str.len num1  ) 1  )  ) ( ite ( = (- 1) ( str.to.int num1  )  ) false true  )  ))

(assert (not ( = ( str.len num1  ) 0  )))
(assert ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( str.len num1  )  ) 0  ))


(check-sat)


(get-value (num1))
(get-value (num2))