(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "ab"  z  ) ( str.++ x1  "addc"  )  )  x2  ) ( str.++ t2  t3  )  ) ( str.++( str.++ z  "ba"  ) ( str.++( str.++( str.++ x2  "dcba"  )  x1  )  t1  )  )  ) )
 ( check-sat )
 