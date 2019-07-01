(set-logic QF_S)

( declare-fun  x () String )
 ( declare-fun  y () String )
 ( assert ( =( str.++( str.++ "c"  "b"  )  x  ) ( str.++( str.++ x  "c"  )  "c"  )  ) )
 ( assert ( =( str.++( str.++ "a"  "d"  )  y  ) ( str.++( str.++ y  "a"  )  "a"  )  ) )
 ( check-sat )
 