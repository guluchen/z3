(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( str.++( str.++( str.++( str.++( str.++ x1  "abec"  )  x2  )  "gf"  ) ( str.++ "ab"  z1  )  ) ( str.++ "cc"  z2  )  ) ( str.++( str.++( str.++( str.++( str.++ x2  "dcba"  )  x1  )  t1  ) ( str.++ z1  "ba"  )  ) ( str.++ z2  "dc"  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( =( str.len x1  ) ( str.len x2  )  ) )
 ( check-sat )
 