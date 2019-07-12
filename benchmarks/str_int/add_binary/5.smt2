(declare-fun a () String)
(declare-fun b () String)

(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert (not ( >= ( + ( + 0 1  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 4)  )  )  )  ) 2  )))

(assert (not ( >= ( + ( str.len b  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  )))

(assert ( >= ( + ( str.len a  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - (- 1) 1  ) 1  ) 1  )  ) 0  ))
(assert (not ( >= ( - ( + ( + ( + 0 1  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 3)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 3)  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + ( + 0 1  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 3)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 3)  )  )  )  ) 2  ))
(assert ( >= ( + ( str.len b  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - (- 1) 1  ) 1  )  ) 0  ))
(assert (not ( >= ( - ( + ( + ( + 0 1  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 2)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 2)  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + ( + 0 1  ) ( str.to.int ( str.at a ( + ( str.len a  ) (- 2)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 2)  )  )  )  ) 2  ))
(assert ( >= ( + ( str.len b  ) ( - (- 1) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - (- 1) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - (- 1) 1  )  ) 0  ))
(assert (not ( >= ( - ( + ( + 0 ( str.to.int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  ) 2  ) 2  )))

(assert ( >= ( + ( + 0 ( str.to.int ( str.at a ( + ( str.len a  ) (- 1)  )  )  )  ) ( str.to.int ( str.at b ( + ( str.len b  ) (- 1)  )  )  )  ) 2  ))
(assert ( >= ( + ( str.len b  ) (- 1)  ) 0  ))
(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))
(assert ( >= ( + ( str.len a  ) (- 1)  ) 0  ))(assert (not ( >= ( + ( str.len a  ) ( - ( - ( - ( - (- 1) 1  ) 1  ) 1  ) 1  )  ) 0  )))
(assert (str.in.re a (re.+ (re.range "0" "1"))))(assert (str.in.re b (re.+ (re.range "0" "1"))))

(check-sat)

(get-value (a))
(get-value (b))