(declare-fun IP () String)

(assert ( str.in.re ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert (not ( not ( = 4 4  )  )))

(assert ( str.contains IP "."  ))(assert ( > ( str.to.int ( str.substr IP 0 ( + ( - ( str.indexof IP "." 0  ) 0  ) 1  )  )  ) 255  ))

(check-sat)

(get-value (IP))