# Z3-SLHV
## Description
Z3-SLHV is a theory solve for Speration Logic with Heap Variable.
Z3-SLHV is implemented as a theory plugin on [Z3](https://github.com/Z3Prover/z3/), which inherit the installation details.

## Configure to enable SELO
Z3-SLHV is used as a back-end solver to support the bounded model checker [SELO](anonymous.4open.science/r/SELO).
It can be installed by following configurations.
CMake >= 3.22 is needed for the compilation

## 1. create release folder
- create folder to receive the  library compiled
```
mkdir z3_slhv_lib
```
## 2. compile library
There are two alternative ways of using shared library or using static library
### configure and compile shared library
- configure Ninja and then compile Z3 into ```z3_slhv_lib``` as ```libz3.so```
```
python3 ./mk_shared_cmake.py
python3 ./shared_recompile_install.py
```
### configure and compile static library
- configure makefile and then compile Z3 into ```z3_slhv_lib``` as ```libz3.a```
```
python3 ./mk_static_cmake.py
python3 ./static_recompile_install.py
```

If configurations are not changed, one can only use recompile script to update.
## TBD
- Enrich README.md
- Update the license accordingly.





