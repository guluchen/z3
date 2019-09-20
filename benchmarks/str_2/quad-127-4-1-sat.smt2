(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( str.++( str.++( str.++( str.++( str.++ x1  "abdc"  )  x2  )  "gf"  ) ( str.++ "ab"  z1  )  ) ( str.++ "cd"  z2  )  ) ( str.++( str.++( str.++( str.++( str.++ x2  "dcba"  )  x1  )  t1  ) ( str.++ z1  "ba"  )  ) ( str.++ z2  "dc"  )  )  ) )
 ( check-sat )
 