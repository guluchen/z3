(set-logic QF_S)

( declare-fun  x312 () String )
 ( declare-fun  x429 () String )
 ( assert ( =( str.++ "abx" ( str.++( str.++ x312  "abbc"  )  x429  )  ) ( str.++ "abx" ( str.++( str.++ x429  "cbca"  )  x312  )  )  ) )
 ( check-sat )
 