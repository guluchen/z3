( declare-fun  x1 () String )
( declare-fun  y1 () String )
( declare-fun  y2 () String )

 ( assert ( =( str.++( str.++ "a" x1  ) "c" )
               (str.++ y1 (str.++ "b" y2)) ))
 ( check-sat )

;sat
;(model
;(define-fun x1 () String "b")
;(define-fun y1 () String "a")
;(define-fun y2 () String "c")
;)