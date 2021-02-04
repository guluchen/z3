(set-logic ALL)
(declare-const name String)
(assert (not (str.contains name "%")))
(assert (not (< (str.len name) 0)))
(assert (> (+ 0 (str.indexof name ":" 0)) 0))
(assert (not (< (+ 0 (str.indexof name ":" 0)) 0)))
(assert (not (= (str.substr name 0 (- (+ 0 (str.indexof name ":" 0)) 0)) "http")))
(assert (not (< (+ 0 (str.indexof name ":" 0)) 0)))
(assert (< 0 (str.len (str.substr name 0 (- (+ 0 (str.indexof name ":" 0)) 0)))))
(assert (< 1 (str.len (str.substr name 0 (- (+ 0 (str.indexof name ":" 0)) 0)))))
(assert (< 2 (str.len (str.substr name 0 (- (+ 0 (str.indexof name ":" 0)) 0)))))
(assert (not (< 3 (str.len (str.substr name 0 (- (+ 0 (str.indexof name ":" 0)) 0))))))
(assert (not (< (+ (+ 0 (str.indexof name ":" 0)) 1) 0)))
(assert (not (< (str.len name) 0)))
(assert (not (= (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "")))
(assert (< 0 (str.len (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))))))
(assert (not (< (+ 0 (str.indexof name ":" 0)) 0)))
(assert (not (= (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "//")))
(assert (str.contains (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "#"))
(assert (not (< (str.len (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "#" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "#" 0)) 0)))
(assert (< (+ (+ 0 (str.indexof (str.substr name (+ (+ 0 (str.indexof name ":" 0)) 1) (- (str.len name) (+ (+ 0 (str.indexof name ":" 0)) 1))) "#" 0)) 1) 0))
(check-sat)
(get-value (name))
