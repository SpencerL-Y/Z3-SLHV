import os

os.system("cd build && rm -rf * && cmake -G \"Ninja\" ../ -DZ3_BUILD_LIBZ3_SHARED=FALSE -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=\"../z3_slhv_lib\"")
