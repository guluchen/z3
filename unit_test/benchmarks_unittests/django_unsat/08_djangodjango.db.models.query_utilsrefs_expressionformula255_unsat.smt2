(set-logic ALL)
(declare-const lookup_parts String)
(declare-const annotations String)
(assert (not (<= (+ (str.len lookup_parts) 1) 1)))
(assert (< 0 (str.len (str.substr lookup_parts 0 (- 1 0)))))
(assert (not (< 1 (str.len (str.substr lookup_parts 0 (- 1 0))))))
(assert (not (str.contains annotations "C")))
(assert (< 0 (str.len (str.substr lookup_parts 0 (- 2 0)))))
(assert (< 1 (str.len (str.substr lookup_parts 0 (- 2 0)))))
(assert (not (< 2 (str.len (str.substr lookup_parts 0 (- 2 0))))))
(assert (not (str.contains annotations "C__D")))
(assert (< 0 (str.len (str.substr lookup_parts 0 (- 3 0)))))
(assert (< 1 (str.len (str.substr lookup_parts 0 (- 3 0)))))
(assert (< 2 (str.len (str.substr lookup_parts 0 (- 3 0)))))
(assert (not (< 3 (str.len (str.substr lookup_parts 0 (- 3 0))))))
(assert (not (str.contains annotations "C__D__A")))
(assert (< 0 (str.len (str.substr lookup_parts 0 (- 4 0)))))
(assert (< 1 (str.len (str.substr lookup_parts 0 (- 4 0)))))
(assert (< 2 (str.len (str.substr lookup_parts 0 (- 4 0)))))
(assert (< 3 (str.len (str.substr lookup_parts 0 (- 4 0)))))
(assert (< 4 (str.len (str.substr lookup_parts 0 (- 4 0)))))
(check-sat)
(get-value (lookup_parts))
(get-value (annotations))
