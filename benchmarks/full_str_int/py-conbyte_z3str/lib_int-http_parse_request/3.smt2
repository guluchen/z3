(declare-fun version () String)


(assert ( str.in.re ( str.substr ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  ) 0 ( - ( str.indexof ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  ) "." 0  ) 0  )  ) ( re.+ ( re.range "0" "9"  )  )  ))

(assert (not ( not ( = 2 2  )  )))

(assert ( str.prefixof "HTTP/" version  ))
(assert (not ( str.in.re ( str.substr ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  ) ( + ( str.indexof ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  ) "." 0  ) 1  ) ( - ( str.len ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  )  ) ( + ( str.indexof ( str.substr version ( + ( str.indexof version "/" 0  ) 1  ) ( - ( str.len version  ) ( + ( str.indexof version "/" 0  ) 1  )  )  ) "." 0  ) 1  )  )  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (version))