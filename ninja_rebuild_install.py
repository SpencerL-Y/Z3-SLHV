import os
import sys

os.system("cd build && ninja install && cd ../z3_slhv_lib && sudo  cp -rf * /usr/local/")
