(declare-fun s () String)


(assert (not ( not ( = ( ite ( str.prefixof "-" ( str.at s 0  )  ) ( - ( str.to.int ( str.substr ( str.at s 0  ) 1 ( - ( str.len ( str.at s 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at s 0  )  )  ) 0  )  )))

(assert ( ite ( str.prefixof "-" ( str.at s 0  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at s 0  ) 1 ( - ( str.len ( str.at s 0  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at s 0  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at s 0  )  )  ) false true  )  ))

(assert (not ( >= 0 1  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert (not ( >= ( + 0 1  ) 1  )))


(check-sat)


(get-value (s))