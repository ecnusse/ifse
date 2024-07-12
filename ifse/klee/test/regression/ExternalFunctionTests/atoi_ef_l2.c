// RUN: %clang %s -emit-llvm -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --recolossus --search=bfs --max-fuzz-solver-time=120s --output-dir=%t.klee-out --external-calls=all %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// CHECK-DAG: atoi
int main() {
  char symvar[2];
  klee_make_symbolic(symvar, sizeof(symvar), "symvar");
  //klee_assume(symvar[1] == '\0');
  symvar[1] = '\0';
  int i = atoi(symvar);
  if (i == 7) {
    // CHECK-DAG: You win!
    printf("You win!\n");
  } else {
    // CHECK-DAG: You lose!
    printf("You lose!\n");
  }
  return 0;
}