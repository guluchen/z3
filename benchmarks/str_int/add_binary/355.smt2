(declare-fun a () String)
(declare-fun b () String)

(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - ( - 0 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - 0 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - 0 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - ( - 0 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - 0 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - 0 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) ( - 0 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - 0 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - 0 1  )  ) 0  ))
(assert ( >= ( + ( str.len b  ) 0  ) 0  ))
(assert ( >= ( + ( str.len a  ) 0  ) 0  ))
(assert ( >= ( + ( str.len a  ) 0  ) 0  ))(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))(assert (str.in.re a (re.+ (re.range "0" "1"))))(assert (str.in.re b (re.+ (re.range "0" "1"))))

(check-sat)

(get-value (a))
(get-value (b))