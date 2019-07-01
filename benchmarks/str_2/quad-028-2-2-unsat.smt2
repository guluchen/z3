(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++( str.++ x1  "abc"  )  x2  )  z  ) ( str.++( str.++( str.++ x2  "bab"  )  x1  )  t  )  ) )
 ( check-sat )
 