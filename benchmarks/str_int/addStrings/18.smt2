(declare-fun num1 () String)
(declare-fun num2 () String)

(assert (not ( not ( = ( div ( + ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 5)  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 4)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 4)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 3)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 10  ) 0  )  )))

(assert (not ( >= ( + ( - ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  ) 1  ) ( str.len num2  )  ) 0  )))

(assert ( >= ( + ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  ) ( str.len num2  )  ) 0  ))
(assert (not ( >= ( + ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  ) ( str.len num1  )  ) 0  )))

(assert (not ( >= ( + ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  )))

(assert ( >= ( + ( - ( - ( - (- 1) 1  ) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + ( - (- 1) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + (- 1) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert (not ( = ( str.len num2  ) 0  )))

(assert (not ( = ( str.len num1  ) 0  )))
(assert ( > ( str.len ( str.++ ( str.++ ( str.++ ( str.++ ( str.++ "" ( int.to.str ( mod ( + ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 5)  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 4)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 4)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 3)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 10  )  )  ) ( int.to.str ( mod ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 4)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 4)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 3)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  ) 10  )  ) 10  )  ) 10  )  )  ) ( int.to.str ( mod ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 3)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 3)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  ) 10  )  ) 10  )  )  ) ( int.to.str ( mod ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 2)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 2)  )  )  )  ) ( div ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  ) 10  )  )  ) ( int.to.str ( mod ( + ( + ( str.to.int ( str.at num1 ( + ( str.len num1  ) (- 1)  )  )  ) ( str.to.int ( str.at num2 ( + ( str.len num2  ) (- 1)  )  )  )  ) 0  ) 10  )  )  )  ) ( ite ( > ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ))(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))