(set-logic ALL)
(declare-const col_name String)
(declare-const used_column_names String)
(declare-const is_relation String)
(assert (not (not (= "a" col_name))))
(assert (not (= is_relation "")))
(assert (str.contains used_column_names "a"))
(assert (str.contains used_column_names "a_0"))
(assert (str.contains used_column_names "a_1"))
(assert (str.contains used_column_names "a_2"))
(check-sat)
(get-value (col_name))
(get-value (used_column_names))
(get-value (is_relation))
