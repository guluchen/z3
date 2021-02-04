(set-logic ALL)
(declare-const needle String)
(declare-const haystack String)
(declare-const msg_prefix String)
(assert (> (str.len (str.++ "" needle)) 0))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (> (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (<= (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0))
(assert (not (= (+ 0 (str.indexof (str.++ "" needle) "<" 0)) (str.len (str.++ "" needle)))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (str.prefixof "<" (str.++ "" needle)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (str.prefixof "</" (str.++ "" needle))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (str.prefixof "<!--" (str.++ "" needle))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (str.prefixof "<?" (str.++ "" needle)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 2) 0)))
(assert (= (str.substr (str.++ "" needle) (+ 0 (str.indexof (str.++ "" needle) "<" 0)) (- (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 2) (+ 0 (str.indexof (str.++ "" needle) "<" 0)))) "<?"))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (> (str.len (str.++ "" needle)) 0))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (> (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (<= (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0))
(assert (not (= (+ 0 (str.indexof (str.++ "" needle) "<" 0)) (str.len (str.++ "" needle)))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (str.prefixof "<" (str.++ "" needle)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (str.prefixof "</" (str.++ "" needle))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (not (str.prefixof "<!--" (str.++ "" needle))))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (str.prefixof "<?" (str.++ "" needle)))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 2) 0)))
(assert (= (str.substr (str.++ "" needle) (+ 0 (str.indexof (str.++ "" needle) "<" 0)) (- (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 2) (+ 0 (str.indexof (str.++ "" needle) "<" 0)))) "<?"))
(assert (not (< (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (< (+ (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) (str.indexof (str.substr (str.++ "" needle) (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) (- (str.len (str.++ "" needle)) (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1))) ">" 0)) 0))
(assert (not (< (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) 0)))
(assert (not (< (str.len (str.++ "" needle)) 0)))
(assert (< (+ (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) (str.indexof (str.substr (str.++ "" needle) (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) (- (str.len (str.++ "" needle)) (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1))) "<" 0)) 0))
(assert (not (< (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 0)))
(assert (< (+ (+ 0 (str.indexof (str.++ "" needle) "<" 0)) 1) 0))
(check-sat)
(get-value (needle))
(get-value (haystack))
(get-value (msg_prefix))
