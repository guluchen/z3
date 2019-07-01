(set-logic QF_S)

( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x7  "abbc"  )  x8  )  z  )  x  ) ( str.++( str.++( str.++( str.++ x8  "cdba"  )  x7  )  "abc"  )  t  )  ) )
 ( check-sat )
 