(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  x3 () String )
 ( assert ( =( str.++( str.++( str.++ x1  "ab"  )  x2  ) ( str.++ x3  "ab"  )  ) ( str.++( str.++( str.++ x2  "ba"  )  x1  ) ( str.++ "ba"  x3  )  )  ) )
 ( assert ( >( str.len x2  )  32000  ) )
 ( check-sat )
 