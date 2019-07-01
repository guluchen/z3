(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++ "ae"  z1  ) ( str.++( str.++ x1  "abdc"  )  x2  )  ) ( str.++ t1  z2  )  ) ( str.++( str.++( str.++ z1  "ba"  ) ( str.++( str.++ x2  t2  )  x1  )  ) ( str.++ z2  "dc"  )  )  ) )
 ( check-sat )
 