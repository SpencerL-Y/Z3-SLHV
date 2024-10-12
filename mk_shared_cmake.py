import os

os.system("mkdir build && cd build && rm -rf * && cmake -G \"Ninja\" ../ -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=\"../z3_slhv_lib\"")
