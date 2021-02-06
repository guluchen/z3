(set-logic QF_S)

( declare-fun  x () String )
 ( assert ( =( str.++( str.++ "c"  x  )  "a"  ) ( str.++( str.++ x  "a"  )  "a"  )  ) )
 ( assert ( >( str.len x  )  3200  ) )
 ( check-sat )
 