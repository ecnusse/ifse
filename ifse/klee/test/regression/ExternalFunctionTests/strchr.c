// RUN: %clang %s -emit-llvm -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --recolossus --search=bfs --max-fuzz-solver-time=120s --output-dir=%t.klee-out --external-calls=all %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// CHECK-DAG: strcmp
int main() {
  char str[2];
  klee_make_symbolic(str, sizeof(str), "array");
  klee_assume(str[1] == '\0');
  char* c = strchr(str, 'e');
  if (c != str) {
    // CHECK-DAG: str is not 'e'
    printf("str[0] is not 'e'\n");
  } else {
    // CHECK-DAG: str is 'e'
    printf("str[0] is 'e'\n");
  }
  // CHECK-DAG: KLEE: done: completed paths = 2
  return 0;
}