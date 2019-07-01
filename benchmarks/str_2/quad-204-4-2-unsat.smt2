(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++ x1  "dcb"  )  x2  ) ( str.++ z2 ( str.++( str.++ t2  t1  )  z1  )  )  ) ( str.++( str.++( str.++ x2  "bce"  )  x1  ) ( str.++ z1 ( str.++ "abc"  z2  )  )  )  ) )
 ( check-sat )
 