(set-logic QF_S)

( declare-fun  x31 () String )
 ( declare-fun  x42 () String )
 ( declare-fun  z () String )
 ( assert ( =( str.++( str.++( str.++ x31  "abbc"  )  x42  )  z  ) ( str.++( str.++( str.++ x42  "cbba"  )  x31  )  "ab"  )  ) )
 ( assert ( >( str.len x31  )  16000  ) )
 ( check-sat )
 