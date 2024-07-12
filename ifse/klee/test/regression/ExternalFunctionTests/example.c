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