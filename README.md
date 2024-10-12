# Z3-SLHV
## Description
Z3-SLHV is a theory solve for Speration Logic with Heap Variable.
Z3-SLHV is implemented as a theory plugin on [Z3](https://github.com/Z3Prover/z3/), which inherit the installation details.

## Configure to enable SELO
Z3-SLHV is used as a back-end solver to support the bounded model checker [SELO](anonymous.4open.science/r/SELO).
It can be installed by following configurations.
- create folder to receive the shared library compiled
```
mkdir z3_slhv_lib
```
- configure CMake using the script
```
python3 ./mk_shared_cmake.py
```
- compile Z3 and install to ./z3_slhv_lib
```
python3 ./recompile_install.py
```

If CMake files are created and remain unchanged in later compilation, one only needs to call the recompling script.

## TBD
- Enrich README.md
- Update the license accordingly.





