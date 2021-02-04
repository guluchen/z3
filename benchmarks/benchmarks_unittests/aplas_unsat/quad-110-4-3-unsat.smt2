(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "ab"  z1  )  "a"  ) ( str.++( str.++ x1  "abdc"  )  x2  )  ) ( str.++( str.++ "cd"  z2  )  t3  )  ) ( str.++( str.++( str.++( str.++ z1  "bv"  )  t2  ) ( str.++( str.++ x2  "dcba"  )  x1  )  ) ( str.++( str.++ z2  "dc"  ) ( str.++ t1  "gh"  )  )  )  ) )
 ( check-sat )
 