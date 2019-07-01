(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x1  "abdc"  )  x2  ) ( str.++( str.++ "ab"  z1  )  "ef"  )  ) ( str.++ t2 ( str.++ "cd"  z2  )  )  ) ( str.++( str.++( str.++( str.++ x2  "dcba"  )  x1  ) ( str.++( str.++ z1  "ba"  )  t1  )  ) ( str.++ z2  "dc"  )  )  ) )
 ( check-sat )
 