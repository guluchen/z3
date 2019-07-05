(declare-fun s () String)

(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  )))

(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) ( + 1 1  )  ) 0  )))

(assert ( < ( + 1 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) ( + 1 1  )  ) 1  ) 0  )))

(assert ( < 1 4  ))
(assert ( < ( + 1 1  ) 4  ))
(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + ( + 1 1  ) 1  )  ) 0  )))

(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) ( + 1 1  )  ) 0  )))

(assert ( < ( + 1 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) 1  ) 0  )))

(assert ( < 1 4  ))
(assert ( < 1 4  ))
(assert ( < ( + 1 1  ) 4  ))
(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  )))

(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  ) 0  )))

(assert ( < ( + 1 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) 1  ) 0  )))

(assert ( < 1 4  ))
(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  )))

(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + 1 1  )  ) 0  )))

(assert ( < ( + 1 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) 1  ) 0  )))

(assert ( < 1 4  ))
(assert ( < ( + 1 1  ) 4  ))
(assert (not ( < ( + ( + ( + 1 1  ) 1  ) 1  ) 4  )))

(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) 0  )))

(assert ( < ( + ( + 1 1  ) 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + 1 1  )  ) 0  )))

(assert ( < ( + 1 1  ) 4  ))
(assert (not ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 0  )))

(assert ( < 1 4  ))
(assert ( < 1 4  ))
(assert ( < 1 4  ))
(assert (not ( > ( str.len s  ) 12  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert (not ( < ( + ( + 1 1  ) 1  ) 4  )))
(assert (str.in.re s (re.+ (re.range "0" "9"))))

(check-sat)

(get-value (s))