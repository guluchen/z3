(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < 0 ( str.len abbr  )  ))

(assert (not ( = ( ite ( str.prefixof "-" ( str.at abbr 1  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 1  ) 1 ( - ( str.len ( str.at abbr 1  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 1  )  )  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.at abbr 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 1  ) 1 ( - ( str.len ( str.at abbr 1  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 1  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert ( < ( + 0 1  ) ( str.len abbr  )  ))

(assert (not ( not ( = ( str.at word 0  ) ( str.at abbr 0  )  )  )))

(assert (not ( >= ( + 0 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < 0 ( str.len abbr  )  ))
(assert ( >= ( + ( + ( + 0 0  ) 1  ) ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 1  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 1  ) 1 ( - ( str.len ( str.at abbr 1  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 1  )  )  )  )  ) ( str.len word  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))