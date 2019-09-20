(declare-fun status () String)


(assert ( ite ( str.prefixof "-" ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  ) 1 ( - ( str.len ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  )  ) false true  )  ))

(assert (not ( not ( = ( str.len ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) 3  )  )))
(assert ( < ( ite ( str.prefixof "-" ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  ) 1 ( - ( str.len ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  )  ) 100  ))


(check-sat)


(get-value (status))