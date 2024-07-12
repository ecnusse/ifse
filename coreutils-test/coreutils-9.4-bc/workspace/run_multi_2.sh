#!/bin/bash

# List of programs to run
programs=("mkfifo"    "mknod"      "mktemp" "mv"
          "nice"      "nl"         "nohup"  "od"
          "paste"     "pathchk"    "pinky"  "pr"
          "printenv"  "printf"     "ptx"    "pwd"
          "readlink"  "rm"         "rmdir"  "runcon"
          "seq"       "setuidgid"  "shred"  "shuf"
          "sleep"     "sort"       "split"  "stat"
          "stty"      "sum"        "sync"   "tac"
          "tail"      "tee"        "touch"  "tr"
          "tsort"     "tty"        "uname"  "unexpand"
          "uniq"      "unlink"     "uptime" "users"
          "wc"        "whoami"     "who"    "yes")


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

