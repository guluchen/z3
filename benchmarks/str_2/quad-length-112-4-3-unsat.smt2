(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "gh"  z1  )  "a"  ) ( str.++( str.++( str.++ x1  "abdc"  )  x2  )  t1  )  ) ( str.++( str.++ "cd"  z2  )  t3  )  ) ( str.++( str.++( str.++( str.++ z1  "ba"  )  t2  ) ( str.++( str.++( str.++ x2  "dcca"  )  x1  )  "xx"  )  ) ( str.++( str.++ z2  "dc"  )  "gh"  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( =( str.len x1  ) ( str.len x2  )  ) )
 ( check-sat )
 