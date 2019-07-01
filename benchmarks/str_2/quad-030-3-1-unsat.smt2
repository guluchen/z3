(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++ x1 ( str.++ t  t  )  )  x2  ) ( str.++( str.++ x2  "b"  )  x1  )  ) )
 ( check-sat )
 