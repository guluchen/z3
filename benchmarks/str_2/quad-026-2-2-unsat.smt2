(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++ x1 ( str.++ "abc"  t  )  )  x2  ) ( str.++( str.++( str.++ x2  "a"  )  x1  )  "ba"  )  ) )
 ( check-sat )
 