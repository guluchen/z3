# Demo of Z3 String Theory Programming


## Building Z3 using CMake
Create a new folder and use cmake to build the demo.
```
mkdir z3-build
cd z3-build
cmake ../
make
```


## Test
Run
```
z3 smt.string_solver=trauc ../Benchmarks/test/test1.smt2
```
