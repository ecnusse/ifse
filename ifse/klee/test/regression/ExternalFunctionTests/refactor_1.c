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

  if (z == 0) 
    // Accually at this point we have turned y1 and y2 into symcrete, beacuse of Fuzz and symcreteMap. 
  {
    printf("z == 0\n");
    if (y1 == 100 && y2 == 200) {
      // Should not reach here!
      printf("z == 0 and y1 == 100 and y2 == 200\n");
    }
  } else {
    printf("z != 0\n");
  }
  return 0;
}