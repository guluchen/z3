(declare-fun IP () String)


(assert (not ( > ( ite ( str.prefixof "-" ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  ) ( - ( str.to.int ( str.substr ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  ) 1 ( - ( str.len ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  ) 1  )  )  )  ) ( str.to.int ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  )  ) 255  )))

(assert ( ite ( str.prefixof "-" ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  ) ( and ( ite ( = (- 1) ( str.to.int ( str.substr ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  ) 1 ( - ( str.len ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  ) 1  )  )  )  ) false true  ) ( > ( str.len ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  ) 1  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  )  )  ) false true  )  ))

(assert ( str.in.re ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = 4 4  )  )))

(assert ( str.contains IP "."  ))
(assert ( = ( str.at ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  ) 0  ) "0"  ))


(check-sat)


(get-value (IP))