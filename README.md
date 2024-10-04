# IFSE

## OverView

IFSE (**I**ntegrating **F**uzz Solving with **S**ymbolic **E**xecution) is an open-souce tool that incorporates various existing techniques to integrate fuzz solving with symbolic execution. As far as we know, IFSE is **the first open-source** SE tool which integrates fuzz solving to address the challenges arised by External Functions(EFs) in real-world applications.




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

### 2. Run docker image

To run the image, use the following command:

```sh
docker run -it ifse-image:stable
```



## Tool environment

The following items can be found in the docker container:

- `Coreutils-test` is the experiment directory, which contains:
  - `coreutils-9.4-bc`, which provides all compiled byte code files of programs in CoreUtils and  all scripts for reproducing evaluation.
  - `Coreutils-9.4-src`, which contains source code of all programs in CoreUtils-9.4.
- `Ifse` contains all source code of our tool, including:
  - klee,  the symbolic execution engine part in which we have extended over 4600 lines of C++ code.
  - Krpk, a highly modularized fuzz solver that contains over 19000 lines of Rust code and can easily support complex theories like floating-point theory and different backend fuzzers.

TODO(根据打包出来的具体情况进行介绍)

## Experiment Detail

We evaluated IFSE on 79 programs in CoreUtils, a a widely used open-source core tool program collection in Unix-like operating system, to demonstrate IFSE's effectiveness when facing real-world applications. We compared IFSE with its baseline KLEE with 4 hours timeout and 8 seconds fuzz solver timeout and calculate the average branch coverage obtained in 10 repeated experiments. 

Due to limited space in the paper, we only presented the overall situation of the experiment. Some supplementary details of the experiment are as follows:

### Line Coverage

IFSE achieves a higher average line coverage for most of the programs (63 programs) ranging from relative 0.8\% to 217.2\% over KLEE and achieves an average line coverage of 54.8\% (while KLEE averaged 42.7\%), which demonstrates the path exploration ability of IFSE. Meanwhile, IFSE achieves relative higher branch coverage of 12.3\% over KLEE. The coverage details of all programs are as follows:

### Branch Coverage

As for branch coverage, IFSE achieves a higher average line coverage for most of the programs (58 programs) ranging from relative TODO\% to TODO\% over KLEE and achieves an average line coverage of TODO\% (while KLEE averaged TODO\%), which demonstrates the branch exploration ability of IFSE.

### Optimizations

As an open-source tool, IFSE employs various optimization strategies to enhance its usability.  Among these strategies, the `splitter` and `predictor` hold relatively significant importance. The former focuses on identifying constraints that are likely to be unsolvable and immediately returning results, thus reducing unnecessary solving. The latter focuses on removing parts of the constraints that do not affect the solving result, thus reducing the search space for solving.

To study their impact on the performance of IFSE, we also conducted ablation experiments. The results show that `splitter` improve the average branch coverage by relative 15.8\% and `predictor` improve the average branch coverage by 3.5\%. Using them together enhances the coverage by relative 23.5\%, indicating that the two optimazations are complementary as the `predictor` may assess the satisfiability of large constraints more accurately when these constraints are scaled down first by the `splitter`. 

在12个程序上的结果需要放到这里（TODO）

### Experiment Reproduction

You can refer to the `README.md` in `coreutils-test` to reproduce our experiment.
