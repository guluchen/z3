(set-logic QF_S)

( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++( str.++ x7  "abbc"  )  x8  )  z  ) ( str.++( str.++( str.++( str.++ x8  "cbba"  )  x7  )  "ab"  )  t  )  ) )
 ( check-sat )
 