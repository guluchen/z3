(declare-fun a () String)
(declare-fun b () String)

(assert (not ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  )))

(assert (not ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  )))

(assert (not ( >= ( + ( str.len b  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  )))

(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert (not ( >= ( + ( str.len b  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  )))

(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert ( >= ( + ( str.len a  ) ( - ( - ( - ( - 0 1  ) 1  ) 1  ) 1  )  ) 0  ))
(assert (not ( >= ( + ( str.len b  ) ( - ( - ( - 0 1  ) 1  ) 1  )  ) 0  )))

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
(assert ( >= ( + ( str.len a  ) 0  ) 0  ))(assert ( = ( div ( + ( div ( + ( div ( + ( div ( + ( div ( + ( + ( div ( + ( + -1 ( str.to.int ( str.at a 0  )  )  ) ( str.to.int ( str.at b 0  )  )  ) 2  ) ( str.to.int ( str.at a -1  )  )  ) ( str.to.int ( str.at b -1  )  )  ) 2  ) ( str.to.int ( str.at a -2  )  )  ) 2  ) ( str.to.int ( str.at a -3  )  )  ) 2  ) ( str.to.int ( str.at a -4  )  )  ) 2  ) ( str.to.int ( str.at a -5  )  )  ) 2  ) 1  ))(assert (str.in.re a (re.+ (re.range "0" "1"))))(assert (str.in.re b (re.+ (re.range "0" "1"))))

(check-sat)

(get-value (a))
(get-value (b))