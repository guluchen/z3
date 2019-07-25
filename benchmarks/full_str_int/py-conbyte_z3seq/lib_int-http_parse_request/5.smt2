(declare-fun version () String)


(assert ( str.prefixof "HTTP/" version  ))
(assert ( not ( = 2 2  )  ))


(check-sat)


(get-value (version))