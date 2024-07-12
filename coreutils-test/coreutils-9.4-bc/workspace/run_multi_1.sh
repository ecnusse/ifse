#!/bin/bash

# List of programs to run
programs=("base64"    "basename"   "cat"    "chcon" 
          "chgrp"     "chmod"      "chown"  "chroot" 
          "cksum"     "comm"       "cp"     "csplit"
          "cut"       "date"       "dd"     "df" 
          "dircolors" "dirname"    "du"     "echo"
          "env"       "expand"     "expr"   "factor" 
          "false"     "fmt"        "fold"   "head" 
          "hostid"    "hostname"   "id"     "ginstall"
          "join"      "kill"       "link"   "ln"
          "logname"   "ls"         "md5sum" "mkdir"
          "[")

# Number of tasks to run at a time
tasks=4

# Loop over the programs
for ((i=0; i<${#programs[@]}; i+=tasks)); do
    # Start the tasks in the background
    for ((j=i; j<i+tasks; j++)); do
        if [[ -n ${programs[j]} ]]; then
            ./run_single_ifse.sh "${programs[j]}" &
        fi
    done
    # Wait for all background jobs to finish
    wait
done

for ((i=0; i<${#programs[@]}; i+=tasks)); do
    # Start the tasks in the background
    for ((j=i; j<i+tasks; j++)); do
        if [[ -n ${programs[j]} ]]; then
            ./run_single_klee.sh "${programs[j]}" &
        fi
    done
    # Wait for all background jobs to finish
    wait
done

