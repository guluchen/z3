(declare-fun f () String)
(declare-fun e () String)
(declare-fun d () String)
(declare-fun c () String)
(declare-fun b () String)
(declare-fun a () String)

(assert (= (str.++ a c) (str.++ c a)))
(assert (= (str.++ c d) "aaaa"))
(assert (not (= c d)))
(assert (not (str.contains b d)))
(assert (not (= e  "aaaa")))
(assert (= (str.++ f a) (str.++ a c)))

(assert (> (str.len a) 0))
(assert (> (str.len b) 0))
(assert (> (str.len c) 0))


(check-sat)

;non-fresh:{a b c d e f: |e|<=4}, f is in the equivalent class of c, so it is here
