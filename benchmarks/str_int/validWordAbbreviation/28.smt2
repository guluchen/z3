(declare-fun word () String)
(declare-fun abbr () String)


(assert (not ( str.in.re ( str.at abbr 4  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) ( str.len abbr  )  ))

(assert (not ( not ( = ( str.at word 4  ) ( str.at abbr 3  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + 0 ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  )  )  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 3  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < ( + ( + ( + 0 1  ) 1  ) 1  ) ( str.len abbr  )  ))

(assert (not ( not ( = ( str.at word 3  ) ( str.at abbr 2  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + 0 ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  )  )  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 2  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < ( + ( + 0 1  ) 1  ) ( str.len abbr  )  ))

(assert (not ( not ( = ( str.at word 2  ) ( str.at abbr 1  )  )  )))

(assert (not ( >= ( + ( + ( + 0 ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  )  )  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 1  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( < ( + 0 1  ) ( str.len abbr  )  ))

(assert ( not ( = ( str.at word 1  ) ( str.at abbr 0  )  )  ))

(assert (not ( >= ( + 0 ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  )  )  ) ( str.len word  )  )))

(assert ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert ( < 0 ( str.len abbr  )  ))

(assert (not ( = ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 0  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 0  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert ( < 0 ( str.len abbr  )  ))
(assert ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 ( + ( * 0 10  ) ( ite ( str.prefixof "-" ( str.at abbr 0  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 0  ) 1 ( - ( str.len ( str.at abbr 0  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 0  )  )  )  )  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  ))


(check-sat)


(get-value (word))
(get-value (abbr))