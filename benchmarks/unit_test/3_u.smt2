(set-logic ALL)

(declare-const str1 String)
(declare-const str2 String)
(declare-const root String)
(declare-const root3 String)

; line 9 and line 10 are semantically-equivalent, but line 9 is ok and line 10 leads to wrong answers.
(assert (str.prefixof "/abc/py-conbyte/" root)); ($root = "/abc/py-conbyte/" + ______)
;(assert (= root (str.++ "/abc/py-conbyte/" root3)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (= str2 (str.substr root (+ (str.indexof root "/" 0) 1) (str.len root)))); ($root = "/" + $str2) or ($root = $str2 if $root not begins with "/")
(assert (= str1 (str.substr str2 (+ (str.indexof str2 "/" 0) 1) (str.len str2)))); ($str2 = "/" + $str1) or ($str2 = $str1 if $str2 not begins with "/")

; line 17 and line 18 are semantically-equivalent, but line 17 is ok and line 18 leads to wrong answers.
;(assert (>= (str.len (str.substr str1 (str.indexof str1 "/" 0) (str.len str1))) 0)); always true
(assert (>= (str.len (str.substr str1 (+ (str.indexof str1 "/" 0) 1) (str.len str1))) 0))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; comment out the following line makes the correct answer become "sat" but trau still remains "unsat."
(assert (= (str.substr str1 0 (str.indexof str1 "/" 0)) "")); (str1 == "") or ("/" not in str1) or (str1.startswith("/"))

(check-sat)
(get-value (root))

