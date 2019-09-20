(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++ t2  z  ) ( str.++( str.++ x1  "ab"  )  x2  )  )  "bacd"  ) ( str.++( str.++ z  "cdba"  ) ( str.++( str.++( str.++ x2  "ba"  )  x1  )  t1  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( >( str.len z  )  32000  ) )
 ( check-sat )
 