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
        opened_created = open(create_filepath, "w")
        for line in opened_file.readlines():
            if "(set-logic QF_ALIA)" in line:
                opened_created.write("(set-logic SLHV)\n")
                # create the common prefix of smt in slhv
                opened_created.write("(declare-hvar emp IntHeap)\n(declare-locvar nil IntLoc)\n(declare-datatype pt_record_0 ((Pt_R_0 (loc IntLoc))))\n(declare-datatype pt_record_1 ((Pt_R_1 (data Int))))")
            else:
                opened_created.write(line)
        opened_file.close()
        opened_created.close()
    