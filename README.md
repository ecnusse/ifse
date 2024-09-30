# IFSE

## OverView

IFSE (**I**ntegrating **F**uzz Solving with **S**ymbolic **E**xecution) is an open-souce tool that incorporates various existing techniques to integrate fuzz solving with symbolic execution. As far as we know, IFSE is **the first open-source** SE tool which focuses on addressing the challenges arised by External Functions(EFs) in real-world applications.




## Tool Setup

We have packaged all the resources related to IFSE into Docker, including the source code of IFSE and the relevant resources required for reproducing the experiments. You can setup IFSE under the following instructions:

### 1. Install Docker

Docker provides tools for deploying applications within containers. Containers are (mostly) isolated from each other and the underlying system. This allows you to make a container, tinker with it and then throw it away when you’re done without affecting the underlying system or other containers.

A Docker container is built from a Docker image. A Docker image encapsulates an application, which in this case is KLEE. This application-level encapsulation is useful because it provides a “portable” and reproducible environment in which to run IFSE.

Follow these links for installation instructions on [Ubuntu](https://docs.docker.com/engine/install/ubuntu/), [OS X](https://docs.docker.com/desktop/install/mac-install/) and [Windows](https://docs.docker.com/desktop/install/windows-install/).

## 2. Pull docker image

We have packaged and pushed the docker image of IFSE to DockerHub, you can pull the docker image by following instruction:

```sh
TODO
```

 This command builds a Docker image named `ifse-image`, which contains the complete runtime environment, source code and evaluation scripts. 

If the image is pulled successfully, you can use the following command to have a check. You should find that an image named `ifse-image` exists.

```
TODO
```



### ~~2. Create docker image~~(To delete)

~~To set up the environment, create the Docker image using the current directory:~~

```sh
docker build -t ifse-image:stable .
```

### 2. Run docker image

To run the image, use the following command:

```sh
docker run -it ifse-image:stable
```



## Tool environment

The following items can be found in the directory:

- `Coreutils-test` is the experiment directory, which contains:
  - `coreutils-9.4-bc`, which provides all compiled byte code files of programs in CoreUtils and  all scripts for reproducing evaluation.
  - `Coreutils-9.4-src`, which contains source code of all programs in CoreUtils-9.4.
- `Ifse` contains all source code of our tool, including:
  - klee,  the symbolic execution engine part in which we have extended over 4600 lines of C++ code.
  - Krpk, a highly modularized fuzz solver that contains over 19000 lines of Rust code and can easily support complex theories like floating-point theory and different backend fuzzers.

TODO(根据打包出来的具体情况进行介绍)

## Experiment Detail

We evaluated IFSE on 79 programs in CoreUtils, a a widely used open-source core tool program collection in Unix-like operating system, to demonstrate IFSE's effectiveness when facing real-world applications. We compared IFSE with its baseline KLEE with 4 hours timeout and 8 seconds fuzz solver timeout and calculate the average branch coverage obtained in 10 repeated experiments. The detail of the result is as follows:
TODO(put coverage detail here)

### Experiment Reproduction

You can refer to the `README.md` in `coreutils-test` to reproduce our experiment.

