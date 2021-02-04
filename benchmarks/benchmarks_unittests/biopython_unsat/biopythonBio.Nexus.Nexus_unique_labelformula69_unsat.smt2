(set-logic ALL)
(declare-const previous_labels String)
(declare-const label String)
(assert (str.contains previous_labels label))
(assert (not (< (str.len label) 0)))
(assert (not (= (+ 0 (str.indexof label "." 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof label "." 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof label "." 0)) 1) 0)))
(assert (not (< (str.len label) 0)))
(assert (not (< (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1) 0)))
(assert (not (< (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1) (- (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1) (- (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1))) "." 0)) (- 1)))
(assert (not (< (str.len (str.substr (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1) (- (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1)))) 0)))
(assert (not (str.prefixof "copy" (str.substr (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1) (- (str.len (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1)))) (+ (+ 0 (str.indexof (str.substr label (+ (+ 0 (str.indexof label "." 0)) 1) (- (str.len label) (+ (+ 0 (str.indexof label "." 0)) 1))) "." 0)) 1))))))
(assert (str.contains previous_labels (str.++ label ".copy")))
(assert (< (str.len (str.++ label ".copy")) 0))
(check-sat)
(get-value (previous_labels))
(get-value (label))
