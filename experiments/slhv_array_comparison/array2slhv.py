import os
import sys

array_bench = "./array_bench"
slhv_bench = "./slhv_bench"

if __name__ == "__main__":
    print(os.getcwd())
    for file in os.listdir(array_bench):
        # print(file)
        filepath = array_bench + "/" + file
        create_filepath = slhv_bench + "/" + file
        opened_file = open(filepath, "r")
        opened_created = open(create_filepath, "a")
        for line in opened_file.readlines():
            if "(set-logic QF_ALIA)" in line:
                opened_created.write("(set-logic SLHV)\n")
            else:
                opened_created.write(line)
        opened_file.close()
        opened_created.close()
    