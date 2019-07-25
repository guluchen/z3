(declare-fun word () String)
(declare-fun abbr () String)


(assert ( ite ( str.prefixof "-" ( str.at abbr 2  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 2  ) 1 ( - ( str.len ( str.at abbr 2  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at abbr 2  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 2  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 2  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = ( str.at word 1  ) ( str.at abbr 1  )  )  )))

(assert (not ( >= ( + ( + ( + 0 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  )))

(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))
(assert (not ( = ( ite ( str.prefixof "-" ( str.at abbr 2  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 2  ) 1 ( - ( str.len ( str.at abbr 2  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 2  )  )  ) 0  )))


(check-sat)


(get-value (word))
(get-value (abbr))