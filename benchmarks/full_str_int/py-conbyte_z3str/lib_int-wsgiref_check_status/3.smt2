(declare-fun status () String)


(assert ( not ( = ( str.len ( str.substr status 0 ( - ( str.indexof status " " 0  ) 0  )  )  ) 3  )  ))


(check-sat)


(get-value (status))