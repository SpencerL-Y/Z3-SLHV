import os
import sys
import time


array_bench = "./array_bench"
slhv_bench = "./slhv_bench"
if __name__ == "__main__":
    for file in os.listdir(array_bench):
        print(file)
        filepath = slhv_bench + "/" + file
        start_time = time.time()
        os.system("z3 " + filepath)
        end_time = time.time()
        print("time: " + str(end_time - start_time))