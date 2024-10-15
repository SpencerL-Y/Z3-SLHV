import os
import time

theory = "slhv"

z3_path = "/media/hfz/1-TB-GT/Github/Z3-slhv/build/z3"
formula_folder = "./z3-{T}-workdir/{T}bench/".format(T = theory)
outputs = "./z3-{T}-workdir/outputs/".format(T = theory)

bug_files = [fn for fn in os.listdir(formula_folder) if fn.endswith("smt2") and fn.find("bug") != -1]
safe_files = [fn for fn in os.listdir(formula_folder) if fn.endswith("smt2") and fn.find("bug") == -1]
result_files = [fn for fn in os.listdir(outputs)]

list.sort(bug_files)
list.sort(safe_files)

print(len(bug_files), len(safe_files))

def has_ran(fname):
  for fn in result_files:
    if fn.find(fname) != -1: return True
  return False

def run_file(file):
  filename = file.rsplit('.', 1)[0]
  if has_ran(filename): return
  # print(filename)
  T1 = time.time()
  result_filename = filename + "_result.txt"
  cmd = z3_path + " -T:900 -memory:40960 " + formula_folder + file + " > " + outputs +  result_filename
  print(cmd)
  os.system(cmd)
  T2 = time.time()
  temp_f = open(outputs + result_filename, "a")
  temp_f.write("Time Consumed: " + str(T2 - T1) + "s")
  temp_f.close()

for file in bug_files:
  run_file(file)
  
for file in safe_files:
  run_file(file)