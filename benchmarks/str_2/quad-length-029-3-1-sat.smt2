(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++ x1 ( str.++ z  z  )  )  x2  ) ( str.++( str.++( str.++ x2  "ba"  )  x1  )  t  )  ) )
 ( assert ( >( str.len x1  )  32000  ) )
 ( check-sat )
 