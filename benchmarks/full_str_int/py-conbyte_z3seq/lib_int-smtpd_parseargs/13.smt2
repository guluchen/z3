(declare-fun arg1 () String)
(declare-fun arg2 () String)


(assert (not ( < ( str.indexof "localhost:8025" ":" 0  ) 0  )))

(assert ( = ( str.len arg2  ) 0  ))

(assert ( = ( str.len arg1  ) 0  ))
(assert (not ( str.in.re ( str.substr "localhost:8025" ( + ( str.indexof "localhost:8025" ":" 0  ) 1  ) ( - ( str.len "localhost:8025"  ) ( + ( str.indexof "localhost:8025" ":" 0  ) 1  )  )  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (arg1))
(get-value (arg2))