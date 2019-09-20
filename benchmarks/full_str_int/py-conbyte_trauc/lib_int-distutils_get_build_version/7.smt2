(declare-fun version () String)


(assert (not ( = ( str.indexof version "MSC v." 0  ) (- 1)  )))
(assert (not ( str.in.re ( str.substr ( str.substr ( str.substr version ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  ) ( - ( str.len version  ) ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  )  )  ) 0 ( - ( str.indexof ( str.substr version ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  ) ( - ( str.len version  ) ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  )  )  ) " " 0  ) 0  )  ) 0 ( - ( + ( str.len ( str.substr ( str.substr version ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  ) ( - ( str.len version  ) ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  )  )  ) 0 ( - ( str.indexof ( str.substr version ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  ) ( - ( str.len version  ) ( + ( str.indexof version "MSC v." 0  ) ( str.len "MSC v."  )  )  )  ) " " 0  ) 0  )  )  ) (- 2)  ) 0  )  ) ( re.+ ( re.range "0" "9"  )  )  )))


(check-sat)


(get-value (version))