(declare-fun num1 () String)
(declare-fun num2 () String)

(assert (not ( not ( = 0 0  )  )))

(assert (not ( >= ( + ( - ( - ( - (- 1) 1  ) 1  ) 1  ) ( str.len num2  )  ) 0  )))

(assert (not ( >= ( + ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  ) 0  ) 10  )))

(assert ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( str.len num2  )  ) 0  ))
(assert (not ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( str.len num1  )  ) 0  )))

(assert (not ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  )))

(assert (not ( >= ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) 1  ) 10  )))

(assert ( >= ( + ( - (- 1) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  ))
(assert ( >= ( + (- 1) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert (not ( = ( str.len num2  ) 0  )))

(assert (not ( = ( str.len num1  ) 0  )))
(assert ( > ( str.len ( str.++ ( str.++ ( str.++ "" ( int.to.str ( + ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  ) 0  )  )  ) ( int.to.str ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) 1  )  )  ) ( int.to.str ( - ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  )  )  ) ( ite ( > ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ))(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))