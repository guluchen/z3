(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++ x1 ( str.++ "ab"  z  )  )  x2  ) ( str.++( str.++ x2 ( str.++ "ba"  t  )  )  x1  )  ) )
 ( assert ( >( str.len x1  )  32000  ) )
 ( check-sat )
 