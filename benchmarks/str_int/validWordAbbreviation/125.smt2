(declare-fun word () String)
(declare-fun abbr () String)

(assert ( str.in.re ( str.at abbr 2  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert ( < ( + ( + 0 1  ) 1  ) ( str.len abbr  )  ))
(assert (not ( = ( str.to.int ( str.at abbr 1  )  ) 0  )))

(assert ( str.in.re ( str.at abbr 1  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert ( < ( + 0 1  ) ( str.len abbr  )  ))
(assert (not ( = ( str.to.int ( str.at abbr 0  )  ) 0  )))

(assert ( str.in.re ( str.at abbr 0  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))
(assert ( < 0 ( str.len abbr  )  ))(assert ( = ( str.to.int ( str.at abbr 2  )  ) 0  ))(assert (str.in.re word (re.+ (re.range "a" "z"))))(assert (str.in.re abbr (re.+ (re.union (re.range "0" "9") (re.range "a" "z")))))

(check-sat)

(get-value (word))
(get-value (abbr))