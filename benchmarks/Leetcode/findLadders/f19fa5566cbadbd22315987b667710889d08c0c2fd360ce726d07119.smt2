(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-option :produce-models true)
(set-option :rewrite-divk true)

(declare-fun beginWord () String)

(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (not (= (ite (= (str.++ (str.++ (str.substr beginWord 0 (- 1 0)) "o") (str.substr beginWord 2 (- (str.len beginWord) 2))) "hot") 1 0) 0))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (not (not (= (ite (<= (str.len beginWord) 0) 1 0) 0)))) (>= 0 0)) (>= (- 1 0) 0)) (>= 2 0)) (>= (- (str.len beginWord) 2) 0)))

(check-sat)

(get-value (beginWord))