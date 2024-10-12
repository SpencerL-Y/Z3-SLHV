import os
import sys

if __name__ == "__main__":
    os.system("cd ./build && make -j16 && cd ../z3_slhv_lib && make install") 
    # && sudo cp -rf * /usr/local/")