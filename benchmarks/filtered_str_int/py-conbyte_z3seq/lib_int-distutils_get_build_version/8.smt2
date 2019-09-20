(declare-fun version () String)


(assert ( = ( str.indexof version "MSC v." 0  ) (- 1)  ))


(check-sat)


(get-value (version))