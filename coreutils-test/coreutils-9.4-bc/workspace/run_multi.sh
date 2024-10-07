#!/bin/bash

# List of programs to run
programs=("base64"    "basename"   "cat"       "chcon"
          "chgrp"     "chmod"      "chown"     "chroot"
          "comm"      "cp"         "csplit"    "false"
          "cut"       "date"       "dd"        "df"
          "du"        "echo"       "dirname"   "link"
          "env"       "expand"     "expr"      "factor"
          "fmt"       "fold"       "ginstall"  "head"
          "id"        "join"       "kill"      "ln"
          "ls"        "md5sum"     "mkdir"     "hostid"
          "mkfifo"    "mknod"      "mktemp"    "mv"
          "nice"      "nl"         "nohup"     "od"
          "paste"     "pathchk"    "pinky"     "pr"
          "printenv"  "printf"     "ptx"       "pwd"
          "readlink"  "rm"         "rmdir"     "runcon"
          "seq"       "shuf"       "split"     "stat"
          "stty"      "sum"        "sync"      "tac"
          "tail"      "tee"        "touch"     "tr"
          "tsort"     "uname"      "unexpand"  "logname"
          "uniq"      "uptime"     "users"     "tty"
          "whoami"     "who"       "unlink")


# Number of tasks to run at a time
tasks=40

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

