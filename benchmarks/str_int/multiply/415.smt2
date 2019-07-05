(declare-fun num1 () String)
(declare-fun num2 () String)

(assert ( > ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert (not ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( + ( str.len num1  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( > ( + ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  )))

(assert ( > ( + ( + ( str.len num2  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num2  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert ( > ( + ( str.len num1  ) ( - 0 1  )  ) ( + 0 ( - 0 1  )  )  ))
(assert (not ( = num2 "0"  )))

(assert (not ( = num1 "0"  )))
(assert (not ( > ( + ( + ( + ( + ( str.len num1  ) ( str.len num2  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( - 0 1  )  ) ( + 1 ( - 0 1  )  )  )))
(assert (str.in.re num1 (re.+ (re.range "0" "9"))))(assert (str.in.re num2 (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (num1))
(get-value (num2))