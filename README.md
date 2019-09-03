# Trau
Trau is a SMT solver focuses on string theory. It builds on top of the Z3 solver.
 
## Building Trau using Cmake
Create a new folder and use cmake to build Trau
```
mkdir trau-build
cd trau-build
cmake /path/to/trau-repo
make
```

## Running Trau 

Try 
```
./z3 smt.string_solver=z3str3 dump_models=true ../benchmarks/Leetcode/addBinary/4a22d6d9c959560f70ab4b2a6065fc377a5402487ae4c5eae36c3f54.smt2
```
A successful execution should give you the following result:

```
sat
(model 
  (define-fun b () String
    "")
  (define-fun a () String
    " ")
)

```
