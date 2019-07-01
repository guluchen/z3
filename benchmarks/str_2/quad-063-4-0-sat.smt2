(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "ab"  z1  ) ( str.++ "fe"  z2  )  ) ( str.++ x1  "abfe"  )  )  x2  ) ( str.++( str.++( str.++ z1  "ba"  ) ( str.++ z2  "ef"  )  ) ( str.++( str.++ x2  "feba"  )  x1  )  )  ) )
 ( check-sat )
 