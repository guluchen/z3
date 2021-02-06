(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  z3 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x1  "ab"  )  x2  ) ( str.++( str.++ z1  t3  )  z2  )  ) ( str.++ "db"  z3  )  ) ( str.++( str.++( str.++( str.++ x2  "ba"  )  x1  ) ( str.++( str.++ z2 ( str.++ t2  t1  )  )  z1  )  ) ( str.++ z3  t4  )  )  ) )
 ( check-sat )
 
