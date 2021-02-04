(set-logic ALL)
(declare-const path String)
(declare-const content_type String)
(declare-const follow Bool)
(declare-const secure Bool)
(assert (not secure))
(assert (not secure))
(assert (= (str.substr (str.++ ";" content_type) 0 (- 1 0)) ";"))
(assert (not (< (str.len (str.++ ";" content_type)) 0)))
(assert (not (< (str.len (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1))) 0)))
(assert (not (> (+ 0 (str.indexof (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) ";" 0)) 0)))
(assert (not (< (+ 0 (str.indexof (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) ";" 0)) 0)))
(assert (not (< (+ 0 (str.indexof (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) ";" 0)) 0)))
(assert (not (< (+ 0 (str.indexof (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) ";" 0)) 0)))
(assert (not (< (str.len (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1))) 0)))
(assert (= (str.substr (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) 0 (- 1 0)) ";"))
(assert (not (< (str.len (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) 1 (- (str.len (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1))) 1))) 0)))
(assert (> (+ 0 (str.indexof (str.substr (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1)) 1 (- (str.len (str.substr (str.++ ";" content_type) 1 (- (str.len (str.++ ";" content_type)) 1))) 1)) ";" 0)) 0))
(check-sat)
(get-value (path))
(get-value (content_type))
(get-value (follow))
(get-value (secure))
