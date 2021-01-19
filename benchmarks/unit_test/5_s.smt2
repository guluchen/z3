(set-logic ALL)
(declare-const used_column_names String)

(assert (str.contains used_column_names "a"))
(assert (str.contains used_column_names "ab"))
(assert (str.contains used_column_names "ac"))

(check-sat)
(get-value (used_column_names))
