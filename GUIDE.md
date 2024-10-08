# User Guide

As a symbolic execution tool based on KLEE, IFSE interacts with users through the command line. This document guides how to use IFSE through the command line.

## Usage

After building, the binaries are located in `/home/user/ifse/build/bin`. Use the following command to run it.

```bash
/home/user/ifse/build/bin/klee --search=bfs --recolossus --recolossus-range=<selected_ranges> --recolossus-external-function=<external_functions>
--recolossus-line=<selected_line> --external-calls=all --max-fuzz-solver-time=<number_of_seconds>s --output-dir=<path_to_output> <path_to_bitcode>
```
For example: There are two source code files and one header file below. We compile them separately and link them into a single bc file, program.bc.

``` shell
clang -I /home/user/ifse/klee/include/ -emit-llvm -g -c main.c -o main.bc
clang -I /home/user/ifse/klee/include/ -emit-llvm -g -c another.c -o another.bc
llvm-link main.bc another.bc -o program.bc
```

``` c
HeaderFile: another.h

1 int another(int x, int y);
2
```

``` c
SourceFile1: another.c

  1 #include <stdlib.h>
  2 #include <stdio.h>
  3 
  4 int another(int x, int y) { 
  5     int r = abs(1);
  6     if (r == 0) {
  7        printf("r is 1\n"); 
  8     } else {
  9        printf("r is not 1\n"); 
 10     }
 11     return x + y;
 12 }  
 13
```

``` c
SourceFile2: main.c

  1 #include "another.h"
  2 int main() {
  3   int x;
  4   klee_make_symbolic(&x, sizeof(x), "x");
  5   int y = abs(x);
  6 
  7   int x2;
  8   klee_make_symbolic(&x2, sizeof(x2), "x2");
  9   int y2 = abs(x2);
 10 
 11   char str[2];
 12   klee_make_symbolic(str, sizeof(str), "array");
 13   klee_assume(str[1] == '\0');
 14   char* c = strchr(str, 'e');
 15 
 16   int _p = another(1, 2);
 17 
 18   return 0;
 19 }
```

| --recolossus-range  |  --recolossus-external-function | --recolossus-line  | explanation  |
|---|---|---|---|
| program.c  | abs,strchr  |   | Does not enable the Colossus algorithm (Hereafter referred to as algorithm) for any external library function (Compilation units should be selected) |
| main.c  | abs,strchr  |   | Enable the algorithm only for abs and strchr appearing in main.c  |
|   | abs  |   | Enable the algorithm only for all abs encountered in the test |
|   |strchr |   | Enable the algorithm only for all strchr encountered in the test  |
| main.c,another.c  | | 5  |Enable the algorithm only for the external library function (if any) that appears at line 5 in main.c and another.c   |
| main.c |abs |   | Enable the algorithm only to abs appearing in main.c  |
| main.c  |abs | 5  | Enable the algorithm for the external library function abs (if any) that appears on the fifth line of the main file  |
| main.c,another.c  | abs|   | Enable the algorithm for using the external library function abs only as it appears in main.c and another.c Note the comma splitting and the strict matching here  |
| main.c  |abs,strchr |   |Enable the algorithm for using the external library functions strchr and abs only as they appear in main.c |

Please note:
1. these three options can only be used if recolossus is enabled.
2. once recolossus is enabled, you must select recolossus-external-function and specify a value for the --max-fuzz-solver-time
3. recolossus-range and recolossus-line are optional.

## Example

The code snippet below is the motivating example `example.c`, which is from the cut program and also used in [the Colossus paper](https://dl.acm.org/doi/10.1145/3293882.3330554).

``` c
// RUN: %clang %s -emit-llvm -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --recolossus --search=bfs --max-fuzz-solver-time=120s --output-dir=%t.klee-out --external-calls=all %t.bc 2>&1 | FileCheck %s
#include "klee/klee.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int getopt(char *arg, const char *optstring) {
  int ch = -1;
  if (arg[0] == '-') {
    // CHECK-DAG: hit 1
    printf("hit 1\n");
    int r = strcmp(arg, "--");
    if (r == 0) {
      // CHECK-DAG: hit 2
      printf("hit 2\n");
      ch = '?';
    }
    if (strcmp(arg, "-") == 0) {
      // CHECK-DAG: hit 3
      printf("hit 3\n");
      ch = '-';
      return ch;
    }
    if (arg[1] == '\0') {
      printf("hit 4\n");
      klee_assert(0 && "sanity check 1");
    }
    char *e = strchr(optstring, arg[1]);
    if (e != NULL) {
      // CHECK-DAG: hit 5
      printf("hit 5\n");
      ch = e[0];
    }
  }
  return ch;
}

int main() {
  char arg[3];
  klee_make_symbolic(arg, sizeof(arg), "arg");
  arg[2] = '\0';
  char optc = getopt(arg, "b:c");
  if (optc != -1) {
    switch (optc) {
    case 'b':
      return 0;
      break;
    case 'c':
      return 1;
      break;
    case '-':
      return 2;
      break;
    case '?':
      return 3;
      break;
    case ':':
      return 4;
      break;
    default:
      break;
    }
    // Yet another sanity check
    if (optc != 'b' && optc != 'c' && optc != '-' && optc != '?' && optc != ':') {
      klee_assert(0 && "sanity check 2");
    }
      
  }
  // CHECK-DAG: KLEE: done: completed paths = 5
}
```

Compile the test case:

``` shell
clang -I /home/user/ifse/klee/include -emit-llvm -g -c example.c -o example.bc
```
And you get the `example.bc` bitcode file.

Now you can run the following command to test `example.c`.

``` shell
/home/user/ifse/build/bin/klee --max-solver-time=30s --recolossus --max-fuzz-solver-time=30 --recolossus-external-function=strchr,strcmp --max-time=600s --search=bfs --external-calls=all example.bc
```
Less than 3 minutes, you can see the output at the terminal. The output is as follows, ifse finds all paths and doesn't trigger the sanity check assertion.

``` shell
KLEE: done: total instructions = 175
KLEE: done: completed paths = 5
KLEE: done: partially completed paths = 0
KLEE: done: generated tests = 5
```
## Evaluation

Please navigate to the `/home/user/coreutils-test` directory and refer to the README file located there.
