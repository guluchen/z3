(declare-fun arg1 () String)
(declare-fun arg2 () String)


(assert ( ite ( str.prefixof "-" ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  ) 1 ( - ( str.len ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  )  )  ) false true  )  ))

(assert ( str.in.re ( str.substr "localhost:25" ( + ( str.indexof "localhost:25" ":" 0  ) 1  ) ( - ( str.len "localhost:25"  ) ( + ( str.indexof "localhost:25" ":" 0  ) 1  )  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( < ( str.indexof "localhost:25" ":" 0  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  ) 1 ( - ( str.len ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  )  ) false true  )  ))

(assert ( str.in.re ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( < ( str.indexof "localhost:8025" ":" 0  ) 0  )))

(assert (not ( = ( str.len arg2  ) 0  )))

(assert ( = ( str.len arg1  ) 0  ))
(assert (not ( >= ( ite ( str.prefixof "-" ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  ) 1 ( - ( str.len ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  )  )  ) 0  )))


(check-sat)


(get-value (arg1))
(get-value (arg2))