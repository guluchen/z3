(set-logic ALL)
(declare-const handle String)
(assert (< 0 (str.len handle)))
(assert (not (< (str.len (str.at handle 0)) 0)))
(assert (not (= (+ 0 (str.indexof (str.at handle 0) " " 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.at handle 0) " " 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.at handle 0) " " 0)) 1) 0)))
(assert (not (< (str.len (str.at handle 0)) 0)))
(assert (not (< (str.len (str.substr (str.at handle 0) (+ (+ 0 (str.indexof (str.at handle 0) " " 0)) 1) (- (str.len (str.at handle 0)) (+ (+ 0 (str.indexof (str.at handle 0) " " 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.at handle 0) (+ (+ 0 (str.indexof (str.at handle 0) " " 0)) 1) (- (str.len (str.at handle 0)) (+ (+ 0 (str.indexof (str.at handle 0) " " 0)) 1))) " " 0)) (- 1)))
(assert (< 1 (str.len handle)))
(assert (not (< (str.len (str.at handle 1)) 0)))
(assert (= (+ 0 (str.indexof (str.at handle 1) " " 0)) (- 1)))
(assert (< 2 (str.len handle)))
(assert (not (< (str.len (str.at handle 2)) 0)))
(assert (= (+ 0 (str.indexof (str.at handle 2) " " 0)) (- 1)))
(assert (< 3 (str.len handle)))
(assert (not (< (str.len (str.at handle 3)) 0)))
(assert (= (+ 0 (str.indexof (str.at handle 3) " " 0)) (- 1)))
(assert (< 4 (str.len handle)))
(assert (not (< (str.len (str.at handle 4)) 0)))
(assert (= (+ 0 (str.indexof (str.at handle 4) " " 0)) (- 1)))
(assert (< 5 (str.len handle)))
(assert (not (< (str.len (str.at handle 5)) 0)))
(assert (not (= (+ 0 (str.indexof (str.at handle 5) " " 0)) (- 1))))
(check-sat)
(get-value (handle))
