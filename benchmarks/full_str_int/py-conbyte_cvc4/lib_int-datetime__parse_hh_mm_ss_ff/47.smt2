(declare-fun tstr () String)


(assert (not ( not ( = ( str.at tstr 2  ) "."  )  )))

(assert ( < ( + 0 2  ) ( str.len tstr  )  ))

(assert ( >= ( + ( + 0 2  ) 1  ) ( str.len tstr  )  ))

(assert ( ite ( str.prefixof "-" ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  ) 1 ( - ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr tstr 0 ( - ( + 0 2  ) 0  )  )  )  ) false true  )  ))

(assert (not ( < ( - ( str.len tstr  ) 0  ) 2  )))
(assert (not ( not ( or ( = 3 ( - ( str.len tstr  ) ( + ( + 0 2  ) 1  )  )  ) ( = 6 ( - ( str.len tstr  ) ( + ( + 0 2  ) 1  )  )  )  )  )))


(check-sat)


(get-value (tstr))