cd /home/user/coreutils-test/coreutils-9.4-src/src

# IFSE
/home/user/ifse/build/bin/klee-replay /home/user/coreutils-test/coreutils-9.4-src/src/$1 /home/user/coreutils-test/coreutils-9.4-bc/workspace/result_all/$1-240min-ifse/*.ktest
# KLEE
# /home/user/recolossus/build/bin/klee-replay /home/user/coreutils-test/coreutils-9.4-src/src/$1 /home/user/coreutils-test/coreutils-9.4-bc/workspace/result_all/$1-240min-original/*.ktest

if [ $1 = "base64" ]; then
    gcov -b base64-basenc | head -3
elif [ $1 = "ginstall" ]; then
    gcov -b install | head -3
elif [ $1 = "md5sum" ]; then
    gcov -b md5sum-digest | head -3
elif [ $1 = "sum" ]; then
    gcov -b sum-digest | head -3
else
    gcov -b $1.c | head -3
fi

rm *.gcda
