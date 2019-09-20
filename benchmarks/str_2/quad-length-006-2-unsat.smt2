(set-logic QF_S)

( declare-fun  x3 () String )
 ( declare-fun  x4 () String )
 ( assert ( =( str.++( str.++ x3  "aabc"  )  x4  ) ( str.++( str.++ x4  "bbaa"  )  x3  )  ) )
 ( assert ( >( str.len x3  )  32000  ) )
 ( assert ( =( str.len x4  ) ( str.len x3  )  ) )
 ( check-sat )
 