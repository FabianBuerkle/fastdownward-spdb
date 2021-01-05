#!/usr/bin/python

import os, sys
import subprocess

path = "/home/fabian/Schreibtisch/fastdownward-spdb"
dirs = os.listdir(path);
"""
cmd = "./build.py"
try:
  subprocess.call(cmd, shell = True)
except:
  raise

cmd2 = './fast-downward.py ../downward-benchmarks-master/gripper/domain.pddl ../downward-benchmarks-master/gripper/prob01.pddl --search "astar(spdb())"'
subprocess.call(cmd2, shell = True)
"""
cmd1 = "rm *.png"
subprocess.call(cmd1, shell = True)
for file in dirs:
  if ".gv" in file:
    pos = str.find(file, ".gv")
    filename = file[0:pos] + ".png"    
    cmd = "dot -Tpng " + file + " -o " + filename
    subprocess.call(cmd, shell = True)    
    print(filename)

cmd2 = "rm *.gv"
subprocess.call(cmd2, shell = True)

