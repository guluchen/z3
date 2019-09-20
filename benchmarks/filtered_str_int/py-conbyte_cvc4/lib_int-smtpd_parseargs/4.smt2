(declare-fun arg1 () String)
(declare-fun arg2 () String)


(assert (not ( < ( str.indexof arg1 ":" 0  ) 0  )))

(assert (not ( = ( str.len arg2  ) 0  )))

(assert (not ( = ( str.len arg1  ) 0  )))
(assert (not ( str.in.re ( str.substr arg1 ( + ( str.indexof arg1 ":" 0  ) 1  ) ( - ( str.len arg1  ) ( + ( str.indexof arg1 ":" 0  ) 1  )  )  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (arg1))
(get-value (arg2))