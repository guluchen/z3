( declare-fun  x () String )
( declare-fun  y () String )
( declare-fun  z () String )

 ( assert ( =( str.++( str.++ x x  ) "aab" )
               (str.++ y (str.++ x z)) ))
 ( check-sat )
