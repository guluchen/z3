(declare-fun IP () String)


(assert (not ( not ( = 4 4  )  )))

(assert ( str.contains IP "."  ))
(assert (not ( str.in.re ( str.substr IP 0 ( - ( str.indexof IP "." 0  ) 0  )  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (IP))