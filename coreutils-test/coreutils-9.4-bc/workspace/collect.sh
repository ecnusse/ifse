cd /home/user/coreutils-test/coreutils-9.4-src/src

/home/user/ifse/build/bin/klee-replay /home/user/coreutils-test/coreutils-9.4-src/src/$1 /home/user/coreutils-data/result_all/$1-120min-ifse/*.ktest

gcov -b $1.c | head -3

rm *.gcda
