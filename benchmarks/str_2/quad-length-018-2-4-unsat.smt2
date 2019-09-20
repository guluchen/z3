(set-logic QF_S)

( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ x7  "abdbc"  )  x8  )  z  ) ( str.++ x1  x2  )  ) ( str.++( str.++( str.++( str.++ x8  "cbbad"  )  x7  )  "ab"  )  t  )  ) )
 ( assert ( >( str.len x7  )  16000  ) )
 ( assert ( =( str.len x7  ) ( str.len x8  )  ) )
 ( check-sat )
 