(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( str.++( str.++ x1  "aa"  )  x2  ) ( str.++( str.++ x2  "ba"  )  x1  )  ) )
 ( assert ( >( str.len x1  )  32000  ) )
 ( check-sat )
 