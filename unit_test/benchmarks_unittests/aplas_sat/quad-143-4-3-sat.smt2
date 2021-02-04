(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x1  "abdc"  )  x2  ) ( str.++( str.++ "ab"  z1  )  t3  )  ) ( str.++( str.++ "cd"  z2  )  t2  )  ) ( str.++( str.++( str.++( str.++ x2  "dcba"  )  x1  ) ( str.++( str.++ z1  "ba"  )  "c"  )  ) ( str.++( str.++ z2  "dc"  )  t1  )  )  ) )
 ( check-sat )
 