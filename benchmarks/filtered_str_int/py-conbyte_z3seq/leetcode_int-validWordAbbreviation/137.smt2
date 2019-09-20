(declare-fun word () String)
(declare-fun abbr () String)


(assert ( = ( ite ( str.prefixof "-" ( str.at abbr 12  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 12  ) 1 ( - ( str.len ( str.at abbr 12  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 12  )  )  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at abbr 12  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 12  ) 1 ( - ( str.len ( str.at abbr 12  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at abbr 12  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 12  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 12  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert ( ite ( str.prefixof "-" ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  ) 1 ( - ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  )  ) false true  )  ))

(assert (not ( = ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at abbr 11  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 11  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 11  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = ( str.at word 10  ) ( str.at abbr 10  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) ( ite ( str.prefixof "-" ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  ) ( - ( str.to.int ( str.substr ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  ) 1 ( - ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  )  )  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 10  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert ( ite ( str.prefixof "-" ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  ) 1 ( - ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  )  )  )  )  ) false true  )  ))

(assert (not ( = ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 9  )  )  ) 0  )))

(assert ( ite ( str.prefixof "-" ( str.at abbr 9  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at abbr 9  ) 1 ( - ( str.len ( str.at abbr 9  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.at abbr 9  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.at abbr 9  )  )  ) false true  )  ))

(assert ( str.in.re ( str.at abbr 9  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = ( str.at word 8  ) ( str.at abbr 8  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 8  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 7  ) ( str.at abbr 7  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 7  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 6  ) ( str.at abbr 6  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 6  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 5  ) ( str.at abbr 5  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 5  ) ( re.+ ( re.range "0" "9"  )  )  )))

(assert (not ( not ( = ( str.at word 4  ) ( str.at abbr 4  )  )  )))

(assert (not ( >= ( + ( + ( + ( + ( + ( + ( + ( + ( + 0 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) 1  ) 0  ) ( str.len word  )  )))

(assert (not ( str.in.re ( str.at abbr 4  ) ( re.+ ( re.range "0" "9"  )  )  )))

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
(assert ( = ( ite ( str.prefixof "-" ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  ) ( - ( str.to.int ( str.substr ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  ) 1 ( - ( str.len ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.++ ( int.to.str 0  ) ( int.to.str ( ite ( str.prefixof "-" ( str.at abbr 11  )  ) ( - ( str.to.int ( str.substr ( str.at abbr 11  ) 1 ( - ( str.len ( str.at abbr 11  )  ) 1  )  )  )  ) ( str.to.int ( str.at abbr 11  )  )  )  )  )  )  ) 0  ))


(check-sat)


(get-value (word))
(get-value (abbr))