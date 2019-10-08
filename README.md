# Z3-Trau

Z3-Trau, which is a new version of [Trau](https://github.com/diepbp/Trau), is a SMT solver focuses on string theory. It builds on top of the Z3 solver.

It is licensed under the [MIT license](LICENSE.txt).

## Build status

| TravisCI |
| -------- |
[![Build Status](https://travis-ci.org/guluchen/z3.svg?branch=new_trau)](https://travis-ci.org/guluchen/z3)

[1]: #building-z3-on-windows-using-visual-studio-command-prompt
[2]: #building-z3-using-make-and-gccclang
[3]: #building-z3-using-cmake
[4]: #z3-bindings

## Building Z3-Trau using Cmake
Create a new folder and use cmake to build Z3-Trau
```
mkdir trau-build
cd trau-build
cmake /path/to/trau-repo
```

## Running Z3-Trau 
Try 
```
./z3 smt.string_solver=trau dump_models=true ../benchmarks/Leetcode/addBinary/4a22d6d9c959560f70ab4b2a6065fc377a5402487ae4c5eae36c3f54.smt2
```

A successful execution should give you the following result:
sat
(model
  (define-fun b () String
    "")
  (define-fun a () String
    " ")
)


