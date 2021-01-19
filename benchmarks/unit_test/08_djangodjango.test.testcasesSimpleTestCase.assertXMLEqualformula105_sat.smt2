(set-logic ALL)
(declare-const xml1 String)
(declare-const xml2 String)
(assert (not (< (str.len xml1) 0)))
(assert (= (+ 0 (str.indexof xml1 "\\n" 0)) (- 1)))
(assert (not (< (str.len xml2) 0)))
(assert (= (+ 0 (str.indexof xml2 "\\n" 0)) (- 1)))
(assert (not (< (str.len (str.++ "" xml1)) 0)))
(assert (not (str.prefixof "<?xml" (str.++ "" xml1))))
(assert (not (< (str.len xml1) 0)))
(assert (not (= (+ 0 (str.indexof xml1 "\n" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof xml1 "\n" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof xml1 "\n" 0)) 1) 0)))
(assert (not (< (str.len xml1) 0)))
(assert (not (< (str.len (str.substr xml1 (+ (+ 0 (str.indexof xml1 "\n" 0)) 1) (- (str.len xml1) (+ (+ 0 (str.indexof xml1 "\n" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr xml1 (+ (+ 0 (str.indexof xml1 "\n" 0)) 1) (- (str.len xml1) (+ (+ 0 (str.indexof xml1 "\n" 0)) 1))) "\n" 0)) (- 1)))
(assert (not (< (str.len xml2) 0)))
(assert (= (+ 0 (str.indexof xml2 "\n" 0)) (- 1)))
(assert (not (= "" xml2)))
(assert (< 0 (str.len xml2)))
(assert (< 1 (str.len xml2)))
(assert (< 2 (str.len xml2)))
(assert (< 3 (str.len xml2)))
(assert (< 4 (str.len xml2)))
(assert (< 5 (str.len xml2)))
(assert (< 6 (str.len xml2)))
(assert (< 7 (str.len xml2)))
(assert (< 8 (str.len xml2)))
(assert (< 9 (str.len xml2)))
(assert (< 10 (str.len xml2)))
(assert (< 11 (str.len xml2)))
(assert (< 12 (str.len xml2)))
(assert (< 13 (str.len xml2)))
(assert (< 14 (str.len xml2)))
(assert (< 15 (str.len xml2)))
(assert (< 16 (str.len xml2)))
(check-sat)
(get-value (xml1))
(get-value (xml2))
