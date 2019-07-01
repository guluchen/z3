(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( str.++( str.++ "bacd"  z  ) ( str.++( str.++ x1  "abc"  )  x2  )  ) ( str.++( str.++ z  "cdba"  ) ( str.++( str.++( str.++ x2  "bba"  )  x1  )  t  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( >( str.len x1  ) ( str.len x2  )  ) )
 ( check-sat )
 