# Build
The complete binary code of IFSE is already provided in`/home/user/ifse/build`. 

This document provides guidance on how to recompile IFSE after modifying its source code

## Compile
Before setting up the development environment, compile the fuzz solver (krpk) first
```bash
cd /home/user/ifse/krpk
cargo build --release
```
Now you have krpk dynamic library in /home/user/ifse/krpk/target/release. After that, you can compile the KLEE project. Firstly, you need make build directory at appropriate place.
```
cd /home/user/ifse/
mkdir build
```
Then navaigate to the build directory and run the following command to configure the project.
```
cd build
/usr/bin/cmake --no-warn-unused-cli -DENABLE_SOLVER_Z3=ON -DZ3_INCLUDE_DIRS=/tmp/z3-4.8.15-install/include/ -DZ3_LIBRARIES=/tmp/z3-4.8.15-install/lib/libz3.so -DCMAKE_BUILD_TYPE=Debug -DCMAKE_BUILD_TYPE:STRING=Debug -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE -DCMAKE_C_COMPILER:FILEPATH=/tmp/llvm-130-install_O_D_A/bin/clang -DCMAKE_CXX_COMPILER:FILEPATH=/tmp/llvm-130-install_O_D_A/bin/clang++ -S/home/user/ifse/klee -B/home/user/ifse/build -G Ninja
```

Now you can run the following command to build the KLEE project.

```
ninja klee
```