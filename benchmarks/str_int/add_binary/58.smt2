(declare-fun a () String)
(declare-fun b () String)


(assert (not ( >= ( + ( str.len a  ) ( - (- 1) 1  )  ) 0  )))

(assert (not ( >= ( + ( + 0 ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at a ( + ( str.len a  ) (- 1)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  )  ) ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) ( - ( str.to.int ( str.substr ( str.at b ( + ( str.len b  ) (- 1)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) 1  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  )  ) 2  )))

(assert ( ite ( str.prefixof "-" ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at b ( + ( str.len b  ) (- 1)  )  ) 1 ( - ( str.len ( str.at b ( + ( str.len b  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len b  ) (- 1)  ) 0  ))

(assert ( ite ( str.prefixof "-" ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) ( ite ( = (- 1) ( str.to.int ( str.substr ( str.at a ( + ( str.len a  ) (- 1)  )  ) 1 ( - ( str.len ( str.at a ( + ( str.len a  ) (- 1)  )  )  ) 1  )  )  )  ) false true  ) ( ite ( = (- 1) ( str.to.int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  ) false true  )  ))

(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))

(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - (- 1) 1  )  ) 0  ))
(assert (str.in.re a (re.+ (re.range "0" "1"))))
(assert (str.in.re b (re.+ (re.range "0" "1"))))


(check-sat)


(get-value (a))
(get-value (b))