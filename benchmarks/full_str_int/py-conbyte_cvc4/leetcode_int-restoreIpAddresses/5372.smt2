(declare-fun s () String)


(assert (not ( = ( str.len ( str.substr s ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( - ( str.len s  ) ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  ) 1 ( - ( str.len ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  ) 1 ( - ( str.len ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )))

(assert ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + 1 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + 1 1  )  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + ( + ( + 1 1  ) ( + 1 1  )  ) 1  ) ( - ( str.len s  ) ( + ( + ( + 1 1  ) ( + 1 1  )  ) 1  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + ( + ( + 1 1  ) ( + 1 1  )  ) 1  ) ( - ( str.len s  ) ( + ( + ( + 1 1  ) ( + 1 1  )  ) 1  )  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s ( + ( + 1 1  ) ( + 1 1  )  ) ( - ( + ( + ( + 1 1  ) ( + 1 1  )  ) 1  ) ( + ( + 1 1  ) ( + 1 1  )  )  )  )  ) 1  ))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )))

(assert ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) 1  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) 1  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + ( + 1 1  ) 1  ) ( - ( + ( + ( + 1 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + ( + 1 1  ) 1  ) ( - ( + ( + ( + 1 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) 1  ) ( + 1 1  )  )  )  ) 1  ))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )))

(assert ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + ( + 1 1  ) 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + ( + 1 1  ) 1  ) ( - ( + ( + ( + 1 1  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + ( + 1 1  ) 1  ) ( - ( + ( + ( + 1 1  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) 1  ) ( + 1 1  )  )  )  ) 1  ))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 1 ( - ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 0 ( - ( + 1 1  ) 0  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 0 ( - ( + 1 1  ) 0  )  )  ) 1  )))

(assert ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + 1 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) 1  ) 0  ))

(assert (not ( <= ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) 255  )))

(assert ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert (not ( <= ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) 255  )))

(assert ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) 255  )))

(assert ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 1 ( - ( + 1 ( + ( + 1 1  ) 1  )  ) 1  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) 1  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) 1  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + 1 ( + 1 1  )  ) ( - ( + ( + 1 ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) ( + 1 ( + 1 1  )  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + 1 ( + 1 1  )  ) ( - ( + ( + 1 ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) ( + 1 ( + 1 1  )  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + 1 ( + 1 1  )  ) ( - ( + ( + 1 ( + 1 1  )  ) ( + 1 1  )  ) ( + 1 ( + 1 1  )  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + 1 ( + 1 1  )  ) ( - ( + ( + 1 ( + 1 1  )  ) ( + 1 1  )  ) ( + 1 ( + 1 1  )  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 1 ( - ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s 1 ( - ( + 1 ( + 1 1  )  ) 1  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + 1 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) 1  ) 0  ))

(assert ( = ( str.at ( str.substr s ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( - ( str.len s  ) ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  )  )  ) 0  ) "0"  ))

(assert (not ( = ( str.len ( str.substr s ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( - ( str.len s  ) ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  )  )  )  ) 1  )))

(assert ( <= ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) ( - ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  )  ) 255  ))

(assert ( ite ( str.prefixof "-" ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  ) 1 ( - ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  )  ) false true  )  ))

(assert (not ( = ( str.at ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  ) 0  ) "0"  )))

(assert (not ( = ( str.len ( str.substr s ( + 1 1  ) ( - ( + ( + 1 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  )  )  ) 1  )))

(assert ( = ( str.len ( str.substr s 1 ( - ( + 1 1  ) 1  )  )  ) 1  ))

(assert ( = ( str.len ( str.substr s 0 ( - 1 0  )  )  ) 1  ))

(assert ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) 3  ))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + 1 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 0  ))

(assert ( str.in.re s ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( > ( str.len s  ) 12  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert ( = ( str.at ( str.substr s ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  ) ( - ( str.len s  ) ( + ( + ( + 1 1  ) ( + 1 1  )  ) ( + 1 1  )  )  )  ) 0  ) "0"  ))


(check-sat)


(get-value (s))