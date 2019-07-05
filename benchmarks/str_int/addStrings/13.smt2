(declare-fun num1 () String)
(declare-fun num2 () String)

(assert ( >= ( + ( - ( - ( - (- 1) 1  ) 1  ) 1  ) ( str.len num2  )  ) 0  ))
(assert (not ( >= ( + ( - ( - ( - (- 1) 1  ) 1  ) 1  ) ( str.len num1  )  ) 0  )))

(assert (not ( >= ( + ( - ( - ( - (- 1) 1  ) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  )))

(assert ( >= ( + ( - ( - (- 1) 1  ) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + ( - (- 1) 1  ) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert ( >= ( + (- 1) ( ite ( < ( str.len num1  ) ( str.len num2  )  ) ( str.len num1  ) ( str.len num2  )  )  ) 0  ))
(assert (not ( = ( str.len num2  ) 0  )))

(assert (not ( = ( str.len num1  ) 0  )))
(assert ( >= ( + ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  ) ( str.len num2  )  ) 0  ))(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))