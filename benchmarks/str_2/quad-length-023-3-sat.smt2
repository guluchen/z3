(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  x3 () String )
 ( assert ( =( str.++( str.++( str.++ x1  "abdc"  )  x2  ) ( str.++ x3  "ab"  )  ) ( str.++( str.++( str.++ x2  "dcba"  )  x1  ) ( str.++ "ba"  x3  )  )  ) )
 ( assert ( >( str.len x1  )  32000  ) )
 ( check-sat )
 