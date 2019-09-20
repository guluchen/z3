(set-logic QF_S)

( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x7  "abbbc"  )  x8  )  z  )  x2  ) ( str.++( str.++( str.++( str.++ x8  "cbcba"  )  x7  )  "ab"  ) ( str.++ x1  t  )  )  ) )
 ( check-sat )
 