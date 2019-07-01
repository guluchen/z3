
( declare-fun  x () String )
 ( declare-fun  y () String )
 ( declare-fun  i () Int )
 ( assert ( =( str.++ "ab"  x  ) ( str.++ x  "ba"  )  ) )
 ( assert ( =( str.++ "c"  y  ) ( str.++ y  "c"  )  ) )
 ( assert ( exists ( ( i Int )  ) ( =( str.len x  ) ( +( * 4  i  )  3  )  ) ) )
 ( assert ( =( str.len x  ) ( * 2 ( str.len y  )  )  ) )
 ( check-sat )
 
