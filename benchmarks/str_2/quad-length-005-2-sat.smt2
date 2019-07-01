(set-logic QF_S)

( declare-fun  x3 () String )
 ( declare-fun  x4 () String )
 ( assert ( =( str.++( str.++ x3  "abbc"  )  x4  ) ( str.++( str.++ x4  "cbba"  )  x3  )  ) )
 ( assert ( >( str.len x3  )  32000  ) )
 ( check-sat )
 