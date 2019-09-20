(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( assert ( =( str.++( str.++( str.++ x1  "dcb"  )  x2  ) ( str.++ z2 ( str.++ "abe"  z1  )  )  ) ( str.++( str.++( str.++ x2  "bcd"  )  x1  ) ( str.++ z1 ( str.++ "fba"  z2  )  )  )  ) )
 ( check-sat )
 