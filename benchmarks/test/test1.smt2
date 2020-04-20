( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( str.++( str.++( str.++( str.++ "ab"  z1  )  "a"  ) ( str.++( str.++( str.++ x1  "abdc"  )  x2  )  t1  )  ) ( str.++( str.++ "cd"  z2  )  t3  )  ) ( str.++( str.++( str.++( str.++ z1  "ba"  )  t2  ) ( str.++( str.++( str.++ x2  "dcba"  )  x1  )  "xx"  )  ) ( str.++( str.++ z2  "dc"  )  "gh"  )  )  ) )
 ( check-sat )

;sat
;(model
;(define-fun x1 () String "")
;(define-fun x2 () String "")
;(define-fun z1 () String "a")
;(define-fun z2 () String "")
;(define-fun t1 () String "")
;(define-fun t2 () String "aabdcc")
;(define-fun t3 () String "cbaxxdcgh")
;)
 
