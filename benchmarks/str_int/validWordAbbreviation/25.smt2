(declare-fun word () String)
(declare-fun abbr () String)

(assert ( < 0 ( str.len abbr  )  ))(assert ( str.in.re ( str.at abbr 0  ) ( re.++ ( re.opt ( str.to.re "-"  )  ) ( re.+ ( re.range "0" "9"  )  )  )  ))(assert (str.in.re word (re.+ (re.range "a" "z"))))(assert (str.in.re abbr (re.+ (re.union (re.range "0" "9") (re.range "a" "z")))))

(check-sat)

(get-value (word))
(get-value (abbr))