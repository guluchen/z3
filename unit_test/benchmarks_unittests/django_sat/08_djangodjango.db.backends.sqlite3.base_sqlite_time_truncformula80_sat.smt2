(set-logic ALL)
(declare-const lookup_type String)
(declare-const dt String)
(declare-const tzname String)
(declare-const conn_tzname String)
(assert (not (= dt "")))
(assert (not (str.contains dt " ")))
(assert (not (= dt "")))
(assert (not (< (str.len dt) 0)))
(assert (not (= (+ 0 (str.indexof dt "-" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof dt "-" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof dt "-" 0)) 1) 0)))
(assert (not (< (str.len dt) 0)))
(assert (not (< (str.len (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 1) 0)))
(assert (not (< (str.len (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) (+ (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 1) (- (str.len (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) (+ (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 1) (- (str.len (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr dt (+ (+ 0 (str.indexof dt "-" 0)) 1) (- (str.len dt) (+ (+ 0 (str.indexof dt "-" 0)) 1))) "-" 0)) 1))) "-" 0)) (- 1)))
(assert (not (= dt "")))
(assert (not (< (str.len dt) 0)))
(assert (not (= (+ 0 (str.indexof dt ":" 0)) (- 1))))
(check-sat)
(get-value (lookup_type))
(get-value (dt))
(get-value (tzname))
(get-value (conn_tzname))
