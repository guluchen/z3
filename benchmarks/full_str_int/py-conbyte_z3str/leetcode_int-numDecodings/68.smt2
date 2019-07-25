(declare-fun s () String)


(assert ( ite ( str.prefixof "-" ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  ) 1 ( - ( str.len ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  )  ) false true  )  ))

(assert ( >= ( + 0 1  ) 1  ))

(assert ( = 0 0  ))

(assert ( not ( = ( ite ( str.prefixof "-" ( str.at s 0  )  ) ( - ( str.to.int ( str.substr ( str.at s 0  ) 1 ( - ( str.len ( str.at s 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at s 0  )  )  ) 0  )  ))

(assert ( ite ( str.prefixof "-" ( str.at s 0  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at s 0  ) 1 ( - ( str.len ( str.at s 0  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at s 0  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at s 0  )  )  ) false true  )  ))

(assert (not ( >= 0 1  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert (not ( < ( ite ( str.prefixof "-" ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  ) 1 ( - ( str.len ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s ( - ( + 0 1  ) 1  ) ( - ( + ( + 0 1  ) 1  ) ( - ( + 0 1  ) 1  )  )  )  )  ) 27  )))


(check-sat)


(get-value (s))