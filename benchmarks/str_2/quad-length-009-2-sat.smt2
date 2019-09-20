(set-logic QF_S)

( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( str.++ "axy" ( str.++( str.++ x312  "abbc"  )  x429  )  ) ( str.++ "axy" ( str.++( str.++ x429  "cbba"  )  x312  )  )  ) )
 ( assert ( >( str.len x312  )  16000  ) )
 ( check-sat )
 