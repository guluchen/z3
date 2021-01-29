(set-logic ALL)
(declare-const model String)
(declare-const pdb_file String)
(declare-const naccess String)
(declare-const temp_path String)
(assert (not (= temp_path "")))
(assert (not (< (str.len temp_path) 0)))
(assert (str.suffixof "/" temp_path))
(assert (not (= (str.++ temp_path "tmpy0tq76fh") "")))
(assert (not (< (str.len (str.++ temp_path "tmpy0tq76fh")) 0)))
(assert (not (str.suffixof "/" (str.++ temp_path "tmpy0tq76fh"))))
(assert (not (< (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) 0)))
(assert (str.prefixof "/" (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")))
(assert (not (= (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "")))
(assert (not (< (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) 0)))
(assert (str.prefixof "/" (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")))
(assert (not (< (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) 0)))
(assert (not (str.prefixof "//" (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb"))))
(assert (not (< (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) 0)))
(assert (not (= (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) 0)))
(assert (not (< (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) 0)))
(assert (not (< (str.len (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1)))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 1) 0)))
(assert (not (< (str.len (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1)))) 0)))
(assert (not (< (str.len (str.substr (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 1)))) 0)))
(assert (= (+ 0 (str.indexof (str.substr (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) (+ (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 1) (- (str.len (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1)))) (+ (+ 0 (str.indexof (str.substr (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1) (- (str.len (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb")) (+ (+ 0 (str.indexof (str.++ (str.++ temp_path "tmpy0tq76fh") "/tmpojq420xr.pdb") "/" 0)) 1))) "/" 0)) 1))) "/" 0)) (- 1)))
(check-sat)
(get-value (model))
(get-value (pdb_file))
(get-value (naccess))
(get-value (temp_path))
