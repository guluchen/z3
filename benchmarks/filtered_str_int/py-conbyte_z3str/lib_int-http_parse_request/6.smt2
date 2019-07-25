(declare-fun version () String)


(assert (not ( str.prefixof "HTTP/" version  )))


(check-sat)


(get-value (version))