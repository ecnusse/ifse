# Reproduce the Experimental Results

Navigate to the directory /home/user/coreutils-test/coreutils-9.4-bc/workspace, where you will find several scripts designed to reproduce the experiment and collect the results:

``` shell
/home/user/coreutils-test/coreutils-9.4-bc/workspace
├── collect.py  # Collect the line/branch coverage results
|
├── collect.sh  # Collect the line/branch coverage results
|
├── run_multi.sh  # Run the whole programs
|
├── run_single_ifse.sh # Run one program using ifse (which you can specify)
|
└── run_single_klee.sh # Run one program using klee (which you can specify)
```

## Step 1: Run a IFSE/KLEE Evaluation

To reproduce the experiment, you can just run the `run_multi.sh` script:

```shell
/home/user/coreutils-test/coreutils-9.4-bc/workspace# ./run_multi.sh
```

After that, We could see the outputs over the `coreutils-9.4-bc/workspace/result_all`.

## Step 2: Replay IFSE/KLEE Generated Test Cases

We can use provided script `collect.py` to collect the line/branch coverage:

``` shell
/home/user/coreutils-test/coreutils-9.4-bc/workspace# python3 collect.py
```

**Note**: During the replay process, certain test cases may introduce noise. For instance, providing `3day` as input to the `sleep` command (which causes a bash program to pause), or feeding `infinity` to `seq` (which generates sequential numbers), can result in non-representative behavior. It is advisable to manually remove such test cases.

After collecting results, you can find `program_output.csv` which stores the results of branch and line coverage in current directory.