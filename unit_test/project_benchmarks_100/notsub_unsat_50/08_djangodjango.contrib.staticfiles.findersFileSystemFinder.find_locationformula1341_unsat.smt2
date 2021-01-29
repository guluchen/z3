(set-logic ALL)
(declare-const root String)
(declare-const path String)
(assert (not (< (str.len path) 0)))
(assert (str.prefixof "<DEFAULT>/" path))
(assert (not (< (str.len path) 0)))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (str.prefixof "/" (str.substr path 10 (- (str.len path) 10))))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (str.prefixof "/" (str.substr path 10 (- (str.len path) 10))))
(assert (not (= (str.substr path 10 (- (str.len path) 10)) "")))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (str.prefixof "/" (str.substr path 10 (- (str.len path) 10))))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (not (str.prefixof "//" (str.substr path 10 (- (str.len path) 10)))))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr path 10 (- (str.len path) 10))) 0)))
(assert (not (< (str.len (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1)))
(assert (= (str.substr (str.substr path 10 (- (str.len path) 10)) 0 (- (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 0)) ""))
(assert (not (= (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 0)) "")))
(assert (not (= (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 0)) ".")))
(assert (not (not (= (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 0)) ".."))))
(assert (str.prefixof "/" (str.substr path 10 (- (str.len path) 10))))
(assert (= (str.substr (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr path 10 (- (str.len path) 10)) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1) (- (str.len (str.substr path 10 (- (str.len path) 10))) (+ (+ 0 (str.indexof (str.substr path 10 (- (str.len path) 10)) "/" 0)) 1))) "/" 0)) 1))) ""))
(assert (str.prefixof "/" (str.substr path 10 (- (str.len path) 10))))
(assert (not (< (str.len root) 0)))
(assert (not (str.prefixof "/" root)))
(assert (not (< (str.len root) 0)))
(assert (not (str.prefixof "/" root)))
(assert (not (= (str.++ "/root/py-conbyte" (str.++ "/" root)) "")))
(assert (not (< (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) 0)))
(assert (str.prefixof "/" (str.++ "/root/py-conbyte" (str.++ "/" root))))
(assert (not (< (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) 0)))
(assert (not (str.prefixof "//" (str.++ "/root/py-conbyte" (str.++ "/" root)))))
(assert (not (< (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) 0)))
(assert (not (= (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) 0)))
(assert (not (< (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1)))
(assert (= (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) 0 (- (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 0)) ""))
(assert (not (= (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 0)) "")))
(assert (not (= (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 0)) ".")))
(assert (not (= (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 0)) "..")))
(assert (not (= (str.substr (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 0)) "")))
(assert (not (= (str.substr (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 0)) ".")))
(assert (not (not (= (str.substr (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) 0 (- (+ 0 (str.indexof (str.substr (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ "/root/py-conbyte" (str.++ "/" root)) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1) (- (str.len (str.++ "/root/py-conbyte" (str.++ "/" root))) (+ (+ 0 (str.indexof (str.++ "/root/py-conbyte" (str.++ "/" root)) "/" 0)) 1))) "/" 0)) 1))) "/" 0)) 0)) ".."))))
(check-sat)
(get-value (root))
(get-value (path))
