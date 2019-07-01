(set-logic QF_S)

( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( str.++( str.++( str.++ "abc"  z  ) ( str.++( str.++ x1  "abvv"  )  x2  )  )  t2  ) ( str.++( str.++ z  "vba"  ) ( str.++( str.++( str.++ x2  "dcba"  )  x1  )  t1  )  )  ) )
 ( assert ( >( str.len x1  )  16000  ) )
 ( assert ( >( str.len z  )  16000  ) )
 ( assert ( =( str.len x1  ) ( str.len x2  )  ) )
 ( check-sat )
 