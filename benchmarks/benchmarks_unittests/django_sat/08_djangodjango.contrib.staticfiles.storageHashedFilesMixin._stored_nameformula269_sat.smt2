(set-logic ALL)
(declare-const name String)
(declare-const hashed_files String)
(assert (not (= name "")))
(assert (not (< (str.len name) 0)))
(assert (not (str.prefixof "/" name)))
(assert (not (< (str.len name) 0)))
(assert (not (= (+ 0 (str.indexof name "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof name "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof name "/" 0)) 1) 0)))
(assert (not (< (str.len name) 0)))
(assert (not (< (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1)))
(assert (not (= (str.substr name 0 (- (+ 0 (str.indexof name "/" 0)) 0)) "")))
(assert (not (= (str.substr name 0 (- (+ 0 (str.indexof name "/" 0)) 0)) ".")))
(assert (not (= (str.substr name 0 (- (+ 0 (str.indexof name "/" 0)) 0)) "..")))
(assert (not (= (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 0)) "")))
(assert (not (= (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 0)) ".")))
(assert (not (not (= (str.substr (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name "/" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name "/" 0)) 1))) "/" 0)) 0)) ".."))))
(check-sat)
(get-value (name))
(get-value (hashed_files))
