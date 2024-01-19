import os
import time
import sys
import matplotlib.pyplot as plt

def write_result_line(key, value):
    f = open('./summary.csv', 'a')
    f.write(key[0]
            + "," + key[1]
            + "," + value[0] 
            + "," + value[1]
            + "," + value[2]
            + "," + value[3]
            + "," + value[4]
            + "," + value[5] + '\n')
    f.close()
  
if __name__ == "__main__":
  output_folder = sys.argv[1]

  output_files = [fn for fn in os.listdir (output_folder)]
  
  ans = {}
  
  for file in output_files:
    print(file)
    info = file.split("_")
    fn = info[0]
    invalid_type = info[1]
    step = info[2]
    expect = info[3]
    
    result = ""
    hts = '0'
    locs = '0'
    tis = '0'
    temp_output_file = open(output_folder + "/" + file, "r")
    is_memout = True
    for line in temp_output_file.readlines():
      if line.find("unsat") == 0:
        is_memout = False
        result = "unsat"
        print("unsat")
      elif line.find("sat") == 0:
        is_memout = False
        result = "sat"
        print("sat")
      if line.find("heap terms") != -1:
        hts = line.strip().split(' ')[-1]
      if line.find("locvars") != -1:
        locs = line.strip().split(' ')[-1]
    temp_output_file.close()
    temp_output_file = open(output_folder + "/" + file, "r")
    if not is_memout:
      for line in temp_output_file.readlines():
        if line.find("Time Consumed") == 0:
          print(line)
          time_in_second = line.strip().split(' ')[-1]
          tis = time_in_second
          print(time_in_second)
    else:
      result = "memout"
      print("memout")
    temp_output_file.close()
    
    if (fn, invalid_type) not in ans:
      ans[(fn, invalid_type)] = []
    
    ans[(fn, invalid_type)].append((step, hts, locs, result, tis, expect))
    
    # write_result_line(file, result, tis)
  
  # for key, value in ans.items():
  #   for v in value:
  #     write_result_line(key, v)
      
  # cumulative graph
  unsat_times = []
  sat_times = []
  all_times = []
  for key, value in ans.items():
    for v in value:
      print(v)
      r = v[3]
      t = v[4].replace('s','0')
      time_val = float(t)
      all_times.append(time_val)
      if r == "sat":
        sat_times.append(time_val)
      elif r == "unsat":
        unsat_times.append(time_val)
  unsat_times.sort()
  sat_times.sort()
  all_times.sort()
  
  all_time_cumulative_xdata = []
  all_time_cumulative_ydata = []
  all_solved_num = 0
  all_time_cumulative_xdata.append(0)
  all_time_cumulative_ydata.append(0)
  for time in all_times:
    if time == 0:
      continue
    all_time_cumulative_xdata.append(time)
    all_time_cumulative_ydata.append(all_solved_num)
    all_solved_num += 1
    all_time_cumulative_xdata.append(time)
    all_time_cumulative_ydata.append(all_solved_num)
  plt.plot(all_time_cumulative_xdata, all_time_cumulative_ydata, color="blue", label="All cases")
  
  unsat_time_cumulative_xdata = []
  unsat_time_cumulative_ydata = []
  unsat_solved_num = 0
  unsat_time_cumulative_xdata.append(0)
  unsat_time_cumulative_ydata.append(0)
  for time in unsat_times:
    unsat_time_cumulative_xdata.append(time)
    unsat_time_cumulative_ydata.append(unsat_solved_num)
    unsat_solved_num += 1
    unsat_time_cumulative_xdata.append(time)
    unsat_time_cumulative_ydata.append(unsat_solved_num)
  plt.plot(unsat_time_cumulative_xdata, unsat_time_cumulative_ydata, color="teal", label="UNSAT cases")
  
  
  sat_time_cumulative_xdata = []
  sat_time_cumulative_ydata = []
  sat_solved_num = 0
  sat_time_cumulative_xdata.append(0)
  sat_time_cumulative_ydata.append(0)
  for time in sat_times:
    sat_time_cumulative_xdata.append(time)
    sat_time_cumulative_ydata.append(sat_solved_num)
    sat_solved_num += 1
    sat_time_cumulative_xdata.append(time)
    sat_time_cumulative_ydata.append(sat_solved_num)
  plt.plot(sat_time_cumulative_xdata, sat_time_cumulative_ydata, color="red", label="SAT cases")
  
  plt.legend()
  # plt.xscale('linear')
  plt.xscale('log')
  plt.axis([0, 420, 0, 300])
  plt.xlabel("solving time bound per case (s)")
  plt.ylabel("number of cases solved within time bound")
  plt.show()
  plt.clf()
  
  # step time points plot
    
  unsat_step_time_pairs = []
  sat_step_time_pairs = []
  all_step_time_pairs = []
  case_to_step_time_pairs = {}
  for key, value in ans.items():
    for v in value:
      print(v)
      r = v[3]
      step = int(v[0])
      t = v[4].replace('s','0')
      time_val = float(t)
      if r == "sat" or r == "unsat":
        all_step_time_pairs.append((step, time_val))
        if key in case_to_step_time_pairs:
          case_to_step_time_pairs[key].append((step, time_val))
          case_to_step_time_pairs[key].sort()
        else:
          case_to_step_time_pairs[key] = []
          case_to_step_time_pairs[key].append((step, time_val))
      if r == "sat":
        sat_step_time_pairs.append((step, time_val))
      elif r == "unsat":
        unsat_step_time_pairs.append((step, time_val))
  
  all_stp_xdata = []
  all_stp_ydata = []
  for p in all_step_time_pairs:
    all_stp_xdata.append(p[0])
    all_stp_ydata.append(p[1])
  plt.scatter(all_stp_xdata, all_stp_ydata, color="blue")
  # for key, value in ans.items():
  #   temp_xdata = []
  #   temp_ydata = []
  #   for p in case_to_step_time_pairs[key]:
  #     temp_xdata.append(p[0])
  #     temp_ydata.append(p[1])
  #   plt.plot(temp_xdata, temp_ydata, color="black")
  plt.xlabel("BMC bounded step size")
  plt.ylabel("solving time (s)")
  plt.show()
  plt.clf()
  
  
  # step hterm points plot
    
  unsat_step_ht_pairs = []
  sat_step_ht_pairs = []
  memout_step_ht_pairs = []
  all_step_ht_pairs = []
  case_to_step_ht_pairs = {}
  for key, value in ans.items():
    for v in value:
      print(v)
      r = v[3]
      step = int(v[0])
      ht_num = int(v[1])
      
      all_step_ht_pairs.append((step, ht_num))
      if key in case_to_step_ht_pairs:
        case_to_step_ht_pairs[key].append((step, ht_num))
        case_to_step_ht_pairs[key].sort()
      else:
        case_to_step_ht_pairs[key] = []
        case_to_step_ht_pairs[key].append((step, ht_num))
      if r == "sat":
        sat_step_ht_pairs.append((step, ht_num))
      elif r == "unsat":
        unsat_step_ht_pairs.append((step, ht_num))
      else:
        memout_step_ht_pairs.append((step, ht_num))
  
  all_shp_xdata = []
  all_shp_ydata = []
  memout_shp_xdata = []
  memout_shp_ydata = []
  for p in all_step_ht_pairs:
    if p not in memout_step_ht_pairs:
      all_shp_xdata.append(p[0])
      all_shp_ydata.append(p[1])
    else:
      memout_shp_xdata.append(p[0])
      memout_shp_ydata.append(p[1])
  memok = plt.scatter(all_shp_xdata, all_shp_ydata, color="blue")
  memnotok = plt.scatter(memout_shp_xdata, memout_shp_ydata, color="red", label="Memory out")
  plt.xlabel("BMC bounded step")
  plt.ylabel("number of heap terms in encoding")
  plt.legend()
  plt.show()
  plt.clf()
  
  