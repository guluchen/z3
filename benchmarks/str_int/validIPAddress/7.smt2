(declare-fun IP () String)


(assert ( ite ( str.prefixof "-" ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) 1 ( - ( str.len ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  )  ) false true  )  ))

(assert ( str.in.re ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( = ( str.at ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) 0  ) "0"  )))

(assert (not ( > ( ite ( str.prefixof "-" ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) 1 ( - ( str.len ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  )  ) 255  )))

(assert ( ite ( str.prefixof "-" ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) 1 ( - ( str.len ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  )  ) false true  )  ))

(assert ( str.in.re ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = 4 4  )  )))

(assert ( str.contains IP "."  ))
(assert ( > ( ite ( str.prefixof "-" ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  ) ( - ( str.to.int ( str.substr ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) 1 ( - ( str.len ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  )  ) 255  ))


(check-sat)


(get-value (IP))