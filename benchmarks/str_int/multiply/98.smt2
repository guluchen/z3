(declare-fun num1 () String)
(declare-fun num2 () String)

(assert ( < ( + ( + ( + ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + ( + ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + ( + ( + 0 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + ( + 0 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( < ( + 0 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))
(assert ( = ( + 0 ( div ( + ( + 0 ( * ( str.to.int ( str.at num1 0  )  ) ( str.to.int ( str.at num2 0  )  )  )  ) ( div ( + ( + ( + 0 ( * ( str.to.int ( str.at num1 1  )  ) ( str.to.int ( str.at num2 0  )  )  )  ) ( * ( str.to.int ( str.at num1 0  )  ) ( str.to.int ( str.at num2 1  )  )  )  ) ( div ( + ( + ( + ( + 0 ( * ( str.to.int ( str.at num1 2  )  ) ( str.to.int ( str.at num2 0  )  )  )  ) ( * ( str.to.int ( str.at num1 1  )  ) ( str.to.int ( str.at num2 1  )  )  )  ) ( * ( str.to.int ( str.at num1 0  )  ) ( str.to.int ( str.at num2 2  )  )  )  ) ( div ( + ( + ( + ( + 0 ( * ( str.to.int ( str.at num1 3  )  ) ( str.to.int ( str.at num2 0  )  )  )  ) ( * ( str.to.int ( str.at num1 2  )  ) ( str.to.int ( str.at num2 1  )  )  )  ) ( * ( str.to.int ( str.at num1 1  )  ) ( str.to.int ( str.at num2 2  )  )  )  ) ( div ( + ( + ( + ( + 0 ( * ( str.to.int ( str.at num1 4  )  ) ( str.to.int ( str.at num2 0  )  )  )  ) ( * ( str.to.int ( str.at num1 3  )  ) ( str.to.int ( str.at num2 1  )  )  )  ) ( * ( str.to.int ( str.at num1 2  )  ) ( str.to.int ( str.at num2 2  )  )  )  ) ( div ( + ( + ( + 0 ( * ( str.to.int ( str.at num1 4  )  ) ( str.to.int ( str.at num2 1  )  )  )  ) ( * ( str.to.int ( str.at num1 3  )  ) ( str.to.int ( str.at num2 2  )  )  )  ) ( div ( + 0 ( * ( str.to.int ( str.at num1 4  )  ) ( str.to.int ( str.at num2 2  )  )  )  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 10  )  ) 0  ))
(assert (not ( > ( + ( + ( + ( + ( + ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( + ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert (not ( > ( + ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num1  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( = num2 "0"  )))

(assert (not ( = num1 "0"  )))
(assert ( < ( + ( + ( + ( + ( + ( + ( + ( + 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) ( + ( str.len num1  ) ( str.len num2  )  )  ))(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))