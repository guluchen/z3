(declare-fun word () String)
(declare-fun abbr () String)


(assert ( ite ( str.prefixof "-" ( str.at abbr 4  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 4  ) 1 ( - ( str.len ( str.at abbr 4  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at abbr 4  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 4  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 4  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = ( str.at word 3  ) ( str.at abbr 3  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 3  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 2  ) ( str.at abbr 2  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 2  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 1  ) ( str.at abbr 1  )  )  )))

(assert (not ( >= ( + ( + ( + 0 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  )))

(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))
(assert ( = ( ite ( str.prefixof "-" ( str.at abbr 4  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 4  ) 1 ( - ( str.len ( str.at abbr 4  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 4  )  )  ) 0  ))


(check-sat)


(get-value (word))
(get-value (abbr))