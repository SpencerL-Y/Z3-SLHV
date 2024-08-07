import os
import sys

if __name__ == "__main__":
    os.system("cd ./build && ninja install && cd ../z3_slhv_lib && sudo cp -rf * /usr/local/")