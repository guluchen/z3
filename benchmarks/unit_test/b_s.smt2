(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)

(assert (= (str.++ a a) (str.++ c c)))
(assert (= (str.++ c d) "aaaa"))
(assert (not (= c d)))
(assert (not (str.contains b d)))

(assert (> (str.len a) 0))
(assert (> (str.len b) 0))
(assert (> (str.len c) 0))


(check-sat)

;non-fresh:{a b c d}
