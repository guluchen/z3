(set-logic QF_S)

( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( str.++( str.++( str.++ x312  "abbc"  )  x429  )  "axy"  ) ( str.++( str.++( str.++ x429  "cbba"  )  x312  )  "axy"  )  ) )
 ( assert ( >( str.len x312  )  12000  ) )
 ( check-sat )
 