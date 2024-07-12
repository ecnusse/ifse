// RUN: %clang %s -emit-llvm -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --recolossus --search=bfs --max-fuzz-solver-time=120s --output-dir=%t.klee-out --external-calls=all %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"
#include <stdio.h>
#include <stdlib.h>
// CHECK-DAG: abs
int main() {
  short x;
  klee_make_symbolic(&x, sizeof(x), "x");
  short y = abs(x);
  if (y == 1) {
    // CHECK-DAG: y is 1
    printf("y is 1\n");
  } else {
    // CHECK-DAG: y is not 1
    printf("y is not 1\n");
  }
  // CHECK-DAG: KLEE: done: completed paths = 2
  return 0;
}