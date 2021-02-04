(set-logic ALL)
(declare-const lines String)
(declare-const results String)
(declare-const num_params String)
(assert (not (<= (str.len lines) 0)))
(assert (< 0 (str.len lines)))
(assert (not (str.contains (str.at lines 0) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 0) "kappa under")))
(assert (< 1 (str.len lines)))
(assert (not (str.contains (str.at lines 1) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 1) "kappa under")))
(assert (< 2 (str.len lines)))
(assert (not (str.contains (str.at lines 2) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 2) "kappa under")))
(assert (< 3 (str.len lines)))
(assert (not (str.contains (str.at lines 3) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 3) "kappa under")))
(assert (< 4 (str.len lines)))
(assert (not (str.contains (str.at lines 4) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 4) "kappa under")))
(assert (< 5 (str.len lines)))
(assert (not (str.contains (str.at lines 5) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 5) "kappa under")))
(assert (< 6 (str.len lines)))
(assert (not (str.contains (str.at lines 6) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 6) "kappa under")))
(assert (< 7 (str.len lines)))
(assert (not (str.contains (str.at lines 7) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 7) "kappa under")))
(assert (< 8 (str.len lines)))
(assert (not (str.contains (str.at lines 8) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 8) "kappa under")))
(assert (< 9 (str.len lines)))
(assert (not (str.contains (str.at lines 9) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 9) "kappa under")))
(assert (< 10 (str.len lines)))
(assert (not (str.contains (str.at lines 10) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 10) "kappa under")))
(assert (< 11 (str.len lines)))
(assert (not (str.contains (str.at lines 11) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 11) "kappa under")))
(assert (< 12 (str.len lines)))
(assert (not (str.contains (str.at lines 12) "Parameters (kappa)")))
(assert (not (str.contains (str.at lines 12) "kappa under")))
(assert (not (< 13 (str.len lines))))
(assert (< 0 (str.len lines)))
(assert (not (str.contains (str.at lines 0) "Rate parameters:")))
(assert (not (str.contains (str.at lines 0) "rate: ")))
(assert (not (str.contains (str.at lines 0) "matrix Q")))
(assert (not (str.contains (str.at lines 0) "alpha")))
(assert (str.contains (str.at lines 0) "rho"))
(check-sat)
(get-value (lines))
(get-value (results))
(get-value (num_params))
