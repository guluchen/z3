(declare-fun f () String)
(declare-fun e () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)

(assert (= (str.++ a a) (str.++ c c)))
(assert (= (str.++ c d) "aaaa"))
(assert (not (= c d)))
(assert (not (str.contains b d)))
(assert (not (= e  "aaaa")))
(assert (= d  "a"))
;(assert (= f  a))

(assert (> (str.len a) 0))
(assert (> (str.len b) 0))
(assert (> (str.len c) 0))


(check-sat)

;non-fresh:{a b e: |e|<=4}, note now we can infer c="aaa" and d="a" so they are fresh
