import os

theory = "slhv"

benchmark = "./new_bench/"
smt2_path = "./outputs/"
generated_path = "./z3-{T}-workdir/{T}bench/".format(T = theory)

files = [fn for fn in os.listdir(benchmark) if fn.endswith("c")]

rm_generated_folder_cmd = "rm -f " + generated_path + "*"
os.system(rm_generated_folder_cmd)

# k
# < k -- 1 3 5
# >= k -- k k + 1
# timeout : 15min
# memory : 40G

invalid_deref = {
  "960521-1-3-mutate" : 1,
  "960521-1-2-mutate" : 7
}

invalid_free = {
  "960521-1-1-mutate" : 2,
  "global-atexit-2-mutate" : 4,
  "test-0232-3" : 17
}

invalid_memleak = {
  "global-atexit-1" : 4,
  "global-atexit-1-mutate" : 3,
  "global-atexit-2" : 4,
  "global-atexit-2-mutate" : 3,
  "global-atexit-3" : 3,
  "test-0019-1-mutate" : 3,
  "test-0019-2-mutate" : 3,
  "test-0019-2" : 3,
  "test-0232-1" : 5
}

safe = {
  "test-0019-1" : [1, 2, 3, 7, 11],
  "test-0232-2" : [1, 2, 3, 6, 13]
}

def generate_smt2(fname, invalid, step, expect):
  rm_outputs_cmd = "rm -f " + smt2_path + "*"
  os.system(rm_outputs_cmd)
  cmd = "sesl -t --sh-mem-leak --add-line-info -bw 32 --bmc-theory {theory} --bmc-step {s} --bmc-smt2-path {smt2path} {c_file}".format(
    fn = fname,
    theory = theory.upper(),
    s = step,
    smt2path = smt2_path,
    c_file = benchmark + fname + ".c"
  )
  print(cmd)
  os.system(cmd)
  assert(os.system('{command} > /dev/null 2>&1'.format(command = cmd)) == 0)
  output_files = [fn for fn in os.listdir(smt2_path) if fn.endswith("smt2")]
  for of in output_files:
    if of.find(invalid) == -1: continue
    suf = of[0 : -5] + "_" + expect
    target_file_name = fname + "_" + suf + ".smt2" 
    cpsmt2cmd = "cp " + smt2_path + of + " " + generated_path + target_file_name
    os.system(cpsmt2cmd)
    print(cpsmt2cmd)

def gen_error_step():
  for file in files:
    fname = file[0 : -2]
    if fname in invalid_deref:
      generate_smt2(fname, "invalidDeref", invalid_deref[fname], "bug")
    if fname in invalid_free:
      generate_smt2(fname, "invalidFree", invalid_free[fname], "bug")
    if fname in invalid_memleak:
      generate_smt2(fname, "invalidMemLeak", invalid_memleak[fname], "bug")

def gen_normal_step(invalid_type, invalid_step):
  for file in files:
    fname = file[0 : -2]
    for step in [2, 3, 5]:
      if fname in invalid_step:
        if step != invalid_step[fname]:
          expect = "safe"
          if step > invalid_step[fname]: expect = "bug"
          generate_smt2(fname, invalid_type, step, expect)
      else:
        generate_smt2(fname, invalid_type, step, "safe")

def gen_safe():
  for file in files:
    fname = file[0 : -2]
    if fname not in safe: continue
    for step in safe[fname]:
      generate_smt2(fname, "invalidDeref", step, "safe")
      generate_smt2(fname, "invalidFree", step, "safe")
      generate_smt2(fname, "invalidMemLeak", step, "safe")


gen_error_step()
gen_normal_step("invalidDeref", invalid_deref)
gen_normal_step("invalidFree", invalid_free)
gen_normal_step("invalidMemLeak", invalid_memleak)
gen_safe()

# invalid derefence
# test-0158-2

# invalid free
# global-atexit-5 3
# test-0232-3 17

# invalid memory leak
# global-atexit-1 5
# global-atexit-2 4
# global-atexit-3 5
# test-0019-2 3
# test-0232-1 9

# unsat
# global-atexit
# test-0019-1
# test-0232-2