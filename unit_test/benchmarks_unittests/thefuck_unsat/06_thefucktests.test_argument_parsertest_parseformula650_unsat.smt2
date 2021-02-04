(set-logic ALL)
(declare-const argv String)
(declare-const result String)
(assert (not (< (str.len argv) 0)))
(assert (not (str.contains (str.substr argv 1 (- (str.len argv) 1)) "THEFUCK_ARGUMENT_PLACEHOLDER")))
(assert (not (= (str.substr argv 1 (- (str.len argv) 1)) "")))
(assert (not (< (str.len (str.at (str.substr argv 1 (- (str.len argv) 1)) 0)) 0)))
(assert (str.prefixof "-" (str.at (str.substr argv 1 (- (str.len argv) 1)) 0)))
(assert (< 0 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 1 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 2 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 3 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 4 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 5 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 6 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 7 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 8 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 9 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 10 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 11 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 12 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 13 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 14 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 15 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 16 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 17 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 18 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (< 19 (str.len (str.substr argv 1 (- (str.len argv) 1)))))
(assert (not (< 20 (str.len (str.substr argv 1 (- (str.len argv) 1))))))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 0) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 0) "")))
(assert (= (str.len (str.at (str.substr argv 1 (- (str.len argv) 1)) 0)) 1))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 1) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 1) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 2) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 2) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 3) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 3) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 4) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 4) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 5) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 5) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 6) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 6) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 7) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 7) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 8) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 8) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 9) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 9) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 10) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 10) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 11) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 11) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 12) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 12) "")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 13) "--")))
(assert (not (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 13) "")))
(assert (= (str.at (str.substr argv 1 (- (str.len argv) 1)) 14) "--"))
(check-sat)
(get-value (argv))
(get-value (result))
