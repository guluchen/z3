(declare-fun IP () String)

(assert (not ( = ( str.at ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) 0  ) "0"  )))

(assert (not ( > ( str.to.int ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  )  ) 255  )))

(assert ( str.in.re ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert (not ( = ( str.at ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) 0  ) "0"  )))

(assert (not ( > ( str.to.int ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) 255  )))

(assert ( str.in.re ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert (not ( not ( = 4 4  )  )))

(assert ( str.contains IP "."  ))(assert (not ( str.in.re ( str.substr ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) ( + ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 1  ) ( + ( - ( str.len ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  )  ) ( + ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 1  )  ) 1  )  ) 0 ( + ( - ( str.indexof ( str.substr ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) ( + ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 1  ) ( + ( - ( str.len ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  )  ) ( + ( str.indexof ( str.substr IP ( + ( str.indexof IP "." 0  ) 1  ) ( + ( - ( str.len IP  ) ( + ( str.indexof IP "." 0  ) 1  )  ) 1  )  ) "." 0  ) 1  )  ) 1  )  ) "." 0  ) 0  ) 1  )  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  )))


(check-sat)

(get-value (IP))