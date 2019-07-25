(declare-fun version () String)


(assert ( str.prefixof "HTTP/" version  ))
(assert (not ( not ( = 1 2  )  )))


(check-sat)


(get-value (version))