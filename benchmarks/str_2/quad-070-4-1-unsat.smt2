(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "ab"  z1  ) ( str.++ t1 ( str.++ "cd"  z2  )  )  ) ( str.++ x1  "abdc"  )  )  x2  ) ( str.++( str.++( str.++ z1  "ba"  ) ( str.++ t1 ( str.++ z2  "dc"  )  )  ) ( str.++( str.++ x2  "dcxa"  )  x1  )  )  ) )
 ( check-sat )
 