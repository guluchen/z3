(declare-fun dtstr () String)


(assert (not ( < ( ite ( str.prefixof "-" ( str.substr dtstr 0 ( - 4 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr dtstr 0 ( - 4 0  )  ) 1 ( - ( str.len ( str.substr dtstr 0 ( - 4 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr dtstr 0 ( - 4 0  )  )  )  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.substr dtstr 0 ( - 4 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr dtstr 0 ( - 4 0  )  ) 1 ( - ( str.len ( str.substr dtstr 0 ( - 4 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr dtstr 0 ( - 4 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr dtstr 0 ( - 4 0  )  )  )  ) false true  )  ))

(assert (not ( not ( = ( str.len dtstr  ) 10  )  )))
(assert ( not ( = ( str.at dtstr 4  ) "-"  )  ))


(check-sat)


(get-value (dtstr))