(declare-fun s () String)


(assert ( > ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) 1  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + ( + 1 1  ) 1  )  ) 1  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + 1 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) ( + 1 1  )  ) 1  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + ( + 1 1  ) 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + 1 1  )  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) ( + 1 1  )  ) 0  ))

(assert (not ( <= ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 3  )))

(assert ( > ( - ( - ( - ( str.len s  ) 1  ) 1  ) 1  ) 0  ))

(assert ( str.in.re s ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( > ( str.len s  ) 12  )))

(assert (not ( = ( str.len s  ) 0  )))
(assert ( <= ( - ( - ( - ( str.len s  ) ( + 1 1  )  ) 1  ) 1  ) 3  ))


(check-sat)


(get-value (s))