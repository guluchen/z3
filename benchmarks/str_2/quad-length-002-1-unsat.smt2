(set-logic QF_S)

( declare-fun  x () String )
 ( assert ( =( str.++( str.++ "c"  "b"  )  x  ) ( str.++( str.++ x  "c"  )  "c"  )  ) )
 ( assert ( >( str.len x  )  32000  ) )
 ( check-sat )
 