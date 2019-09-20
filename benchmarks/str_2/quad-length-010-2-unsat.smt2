(set-logic QF_S)

( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( str.++ "abx" ( str.++( str.++ x312  "abbc"  )  x429  )  ) ( str.++ "abx" ( str.++( str.++ x429  "cbca"  )  x312  )  )  ) )
 ( assert ( >( str.len x312  )  16000  ) )
 ( assert ( =( str.len x312  ) ( str.len x429  )  ) )
 ( check-sat )
 