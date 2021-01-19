(set-logic ALL)
(declare-const path String)
(declare-const s1 String)
(declare-const HAHA Int)
(declare-const s2 String)

(assert (= s1 (str.++ "//AA/" path))) 
(assert (= HAHA (+ (str.indexof s1 "/" 0) 1)))
(assert (= s2 (str.substr s1 HAHA (str.len s1)))) 
(assert (>= (str.indexof (str.substr s2 (+ (str.indexof s2 "/" 0) 1) (str.len s2)) "/" 0) (- 1))) ;should be valid

(check-sat)
