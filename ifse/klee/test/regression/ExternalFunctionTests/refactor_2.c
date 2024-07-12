// RUN: %clang %s -emit-llvm -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --recolossus --search=bfs --max-fuzz-solver-time=120s --output-dir=%t.klee-out --external-calls=all %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"
#include <stdio.h>
#include <stdlib.h>
// CHECK-DAG: abs
int main() {
  int y1;
  klee_make_symbolic(&y1, sizeof(y1), "y1");
  int y2;
  klee_make_symbolic(&y2, sizeof(y2), "y2");

  int z = abs(y1 + y2);

  if (z == 0) {
    printf("z == 0\n");
    if (y1 == 100 && y2 == -100) {
      // Although SMT failed, the Fuzz can give the right value
      // Set more max solver time and max time
      printf("z == 0 and y1 == 100 and y2 == -100\n");
    }
  } else {
    printf("z != 0\n");
  }
  return 0;
}