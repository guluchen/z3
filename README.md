# Trau
Trau is a SMT solver focuses on string theory. It builds on top of the Z3 solver.

## Requirements

Trau is know to work under Linux using g++(>= 6) and OSX 
using XCode(>= 9.4) with C11 support.   
Before attempting to build Trauc, you need to have the 
following installed
- cmake
- [libgmp](https://gmplib.org/)
- [libmpfr](https://www.mpfr.org/)
- [ppl](https://www.bugseng.com/ppl)

For Ubuntu16 or 18, you can use `apt-get` to install libgmp,  
ppl and libmpfr.
```
~$ sudo apt-get install libgmp-dev libmpfr-dev ppl-dev
```

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
z3 smt.string_solver=z3str3 dump_models=true ../benchmarks/Leetcode/addBinary/4a22d6d9c959560f70ab4b2a6065fc377a5402487ae4c5eae36c3f54.smt2
```
A successful execution should give you the following result:

```
sat
(model 
  (define-fun b () String
    "")
  (define-fun a () String
    "A")
)

```
