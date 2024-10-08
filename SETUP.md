# Overview

This document helps you to set up IFSE by docker and how to recompile IFSE inside the docker.

## Tool Setup

We have packaged all the resources related to IFSE into Docker, including the source code of IFSE and the relevant resources required for reproducing the experiments. 

You can setup IFSE under the following instructions:

### 1. Install Docker

Docker provides tools for deploying applications within containers. Containers are (mostly) isolated from each other and the underlying system. This allows you to make a container, tinker with it and then throw it away when you’re done without affecting the underlying system or other containers.

A Docker container is built from a Docker image. A Docker image encapsulates an application, which in this case is KLEE. This application-level encapsulation is useful because it provides a “portable” and reproducible environment in which to run IFSE.

Follow these links for installation instructions on [Ubuntu](https://docs.docker.com/engine/install/ubuntu/), [OS X](https://docs.docker.com/desktop/install/mac-install/) and [Windows](https://docs.docker.com/desktop/install/windows-install/).



### 2. Pull docker image

We have packaged and pushed the docker image of IFSE to DockerHub, you can pull the docker image by following instruction:

```sh
docker pull ifseanalysis/ifse-image:stable
```

 This command builds a Docker image named `ifse-image`, which contains the complete runtime environment, source code and evaluation scripts. 

If the image is pulled successfully, you can use the following command to have a check. You should find that an image named `ifse-image` exists.

```sh
$ docker images
REPOSITORY                                     TAG       IMAGE ID       CREATED         SIZE
ifseanalysis/ifse-image                       stable    a78bcd0cfa67   2 months ago    11.7GB
```



### 3. Run docker image

To run the image, use the following command:

```sh
docker run -it ifseanalysis/ifse-image:stable 
```



### 4. Using IFSE

We have packaged the **executable artifacts** of IFSE in Docker. You can refer to `README.md` under `\home\user\ifse` to use IFSE.



## Tool Structure

After starting the docker container, the following items can be found in your environment:


```Shell
/home/user/
|-- coreutils-test # Evaluation Directory
|   |
|   |-- coreutils-9.4-bc # All compiled byte code files of programs in CoreUtils-9.4 and  all scripts for reproducing evaluation.
|   |
|   |-- coreutils-9.4-src # Source code of all programs in CoreUtils-9.4.
|   |
|-- ifse # All source code and executable artifacts of IFSE
|   |
|   |-- build # Compiled binary code of IFSE
|   |
|   |-- klee # The symbolic execution engine part in which we have extended over 4600 lines of C++ code.
|   |
|   |-- krpk # A highly modularized fuzz solver that contains over 11000 lines of Rust code and can easily support complex theories like floating-point theory and different backend fuzzers.
```

## Recompile
The complete binary code of IFSE is already provided in`/home/user/ifse/build`. 

This section provides guidance on how to recompile IFSE after modifying its source code

### Instructions
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