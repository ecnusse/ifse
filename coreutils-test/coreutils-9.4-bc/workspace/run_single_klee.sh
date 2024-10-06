KLEE_OUT_DIR_ALL=${PWD}/"result_all"

mkdir -p ${KLEE_OUT_DIR_ALL}

KLEE_EXE_PATH="/home/user/ifse/build/bin/klee"
MAX_EXE_TIME="240min"
SEARCH="bfs"
ARGS="--sym-args 0 1 10 --sym-args 0 2 7 --sym-files 1 8 --sym-stdin 8 --sym-stdout"
EXTERNAL_FUNCTION="memchr,memcpy,memset,strchr,strcoll,strcspn,strlen,strncmp,strpbrk,strspn,strtok,memcmp,memmove,strcat,strcmp,strcpy,strerror,strncat,strncpy,strrchr,strstr,strxfrm"

cd "../bcfiles"

driver_name=$1

echo " Running ======== > "${driver_name}

if [ ${driver_name} = "dd" ];then
ARGS="--sym-args 0 3 10 --sym-files 1 8 --sym-stdin 8 --sym-stdout"
elif [ ${driver_name} = "dircolors" ];then
ARGS="--sym-args 0 3 10 --sym-files 2 12 --sym-stdin 12 --sym-stdout"
elif [ ${driver_name} = "echo" ];then
ARGS="--sym-args 0 4 10 --sym-files 2 20 --sym-stdin 20 --sym-stdout"
elif [ ${driver_name} = "expr" ];then
ARGS="--sym-args 0 1 10 --sym-args 0 3 2 --sym-stdout"
elif [ ${driver_name} = "mknod" ];then
ARGS="--sym-args 0 1 10 --sym-args 0 3 2 --sym-files 1 8 --sym-stdin 8 --sym-stdout"
elif [ ${driver_name} = "od" ];then
ARGS="--sym-args 0 3 10 --sym-files 2 12 --sym-stdin 12 --sym-stdout"
elif [ ${driver_name} = "pathchk" ];then
ARGS="--sym-args 0 1 2 --sym-args 0 1 30 --sym-files 1 8 --sym-stdin 8 --sym-stdout"
elif [ ${driver_name} = "printf" ];then
ARGS="--sym-args 0 3 10 --sym-files 2 12 --sym-stdin 12 --sym-stdout"
fi

KLEE_OUT_DIR=${KLEE_OUT_DIR_ALL}/${driver_name}"-"${MAX_EXE_TIME}"-original"
rm -rf ${KLEE_OUT_DIR}
TIME_LOG_TXT=${KLEE_OUT_DIR}/"execute_time.txt"

# run klee to get Ktest inputs
start_second=$(date +%s)

${KLEE_EXE_PATH} \
    --max-solver-time=30s \
    --search=${SEARCH} \
    --libc=uclibc --posix-runtime \
    --watchdog --max-time=${MAX_EXE_TIME}  \
    --output-dir=${KLEE_OUT_DIR} \
    --external-calls=all \
    --only-output-states-covering-new \
    ${driver_name}".bc" ${ARGS} &> ${KLEE_OUT_DIR_ALL}/${driver_name}-original-"error.log"
wait
end_second=$(date +%s)
touch ${TIME_LOG_TXT}
echo " "$((end_second-start_second))" " > ${TIME_LOG_TXT}

# delete 'assembly.ll','run.istats' in klee-output, because their size are too large
rm -f ${KLEE_OUT_DIR}/assembly.ll  ${KLEE_OUT_DIR}/run.istats

