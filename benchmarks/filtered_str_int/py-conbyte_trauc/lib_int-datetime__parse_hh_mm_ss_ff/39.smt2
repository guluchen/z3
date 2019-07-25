(declare-fun tstr () String)


(assert (not ( < ( ite ( str.prefixof "-" ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  ) 1 ( - ( str.len ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  )  ) 0  )))

(assert (not ( > ( ite ( str.prefixof "-" ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  ) 1 ( - ( str.len ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  )  ) 60  )))

(assert (not ( < ( ite ( str.prefixof "-" ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  ) 1 ( - ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  )  ) 0  )))

(assert (not ( > ( ite ( str.prefixof "-" ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  ) 1 ( - ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  )  ) 12  )))

(assert (not ( < ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( str.len tstr  )  )))

(assert ( >= ( + ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) 1  ) ( str.len tstr  )  ))

(assert ( ite ( str.prefixof "-" ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  ) 1 ( - ( str.len ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  )  ) false true  )  ))

(assert (not ( < ( - ( str.len tstr  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  ) 2  )))

(assert (not ( not ( = ( str.substr tstr ( + ( + ( + 0 2  ) 1  ) 2  ) ( - ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( + ( + ( + 0 2  ) 1  ) 2  )  )  ) ":"  )  )))

(assert (not ( >= ( + 0 1  ) 2  )))

(assert (not ( >= ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( str.len tstr  )  )))

(assert ( ite ( str.prefixof "-" ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  ) 1 ( - ( str.len ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr tstr ( + ( + 0 2  ) 1  ) ( - ( + ( + ( + 0 2  ) 1  ) 2  ) ( + ( + 0 2  ) 1  )  )  )  )  ) false true  )  ))

(assert (not ( < ( - ( str.len tstr  ) ( + ( + 0 2  ) 1  )  ) 2  )))

(assert (not ( not ( = ( str.substr tstr ( + 0 2  ) ( - ( + ( + 0 2  ) 1  ) ( + 0 2  )  )  ) ":"  )  )))

(assert (not ( >= 0 2  )))

(assert (not ( >= ( + ( + 0 2  ) 1  ) ( str.len tstr  )  )))

(assert ( ite ( str.prefixof "-" ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  ) 1 ( - ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  )  ) false true  )  ))

(assert (not ( < ( - ( str.len tstr  ) 0  ) 2  )))
(assert (not ( > ( ite ( str.prefixof "-" ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  ) 1 ( - ( str.len ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr tstr ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) ( - ( + ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  ) 2  ) ( + ( + ( + ( + 0 2  ) 1  ) 2  ) 1  )  )  )  )  ) 60  )))


(check-sat)


(get-value (tstr))