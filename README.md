# Trauc

Trauc is a theorem prover based on [Z3](https://github.com/Z3Prover/z3)
## Build status

| TravisCI |
| -------- |
|[![Build Status](https://travis-ci.org/guluchen/z3.svg?branch=master)](https://travis-ci.org/guluchen/z3)

## Requirements

Trau is know to work under Linux using g++(>= 6) and OSX 
using XCode(>= 9.4) with C11 support.   
Before attempting to build Trauc, you need to have the 
following installed
- cmake
- [libgmp](https://gmplib.org/)
- [libmpfr](https://www.mpfr.org/)
- [ppl](https://www.bugseng.com/ppl)
- [openfst](http://www.openfst.org/twiki/bin/view/FST/WebHome)
- [apron](http://apron.cri.ensmp.fr/library)

For Ubuntu16 or 18, you can use `apt-get` to install libgmp,  
ppl and libmpfr.
```
~$ sudo apt-get install libgmp-dev libmpfr-dev ppl-dev
``` 
To install openfst and apron, you can refer to the 
[travis-ci build script](/contrib/ci/scripts/install-lib.sh).

For OSX users, you can refer to
[this script](/contrib/ci/scripts/install-ppl.sh) to install ppl.

## Building Z3 using CMake
Create a new folder and use cmake to build Trauc.
```
mkdir trauc-build
cd trauc-build
cmake /path/to/trauc-repo
make
```
Refer to [README-CMake.md](/README-CMake.md) for more options
on cmake.
