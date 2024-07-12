//===-- FuzzingSolver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "FuzzingSolver.h"

#include "AddressSpace.h"
#include "ExecutionState.h"

#include "klee/ADT/Ref.h"
#include "klee/Config/Version.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Solver/SolverCmdLine.h"
#include "klee/Statistics/Statistics.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Expr/SymcreteAndExtOpFilter.h"
#include "klee/Expr/ExprUtil.h"

#include "CoreStats.h"
#include "klee/Support/ErrorHandling.h"
#include "llvm/ADT/None.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

using namespace klee;
using namespace llvm;

bool FuzzingSolver::mustBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

bool FuzzingSolver::mustBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                               bool &result, SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

bool FuzzingSolver::mayBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                             bool &result, SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

bool FuzzingSolver::mayBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

bool FuzzingSolver::getValue(const ConstraintSet &constraints, ref<Expr> expr,
                            ref<ConstantExpr> &result,
                            SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

bool FuzzingSolver::getInitialValues(
    const ConstraintSet &constraints, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char>> &result,
    SolverQueryMetaData &metaData) {
  if (objects.empty())
    return true;

  bool success = solver->getInitialValues(
      Query(constraints, ConstantExpr::alloc(1, Expr::Bool)), objects, result);

  return success;
}

std::pair<ref<Expr>, ref<Expr>>
FuzzingSolver::getRange(const ConstraintSet &constraints, ref<Expr> expr,
                       SolverQueryMetaData &metaData) {
  assert(0 && "Unimplemented Fuzzing Solver API");
}

// The splitting algorithm really needs thoughts and validation.
ConstraintSet FuzzingSolver::splitConstraints(const ConstraintSet& constraints, ref<Expr> condition,
                                  std::vector<const Array*> &extras) {
  ConstraintSet split;
  auto tmpSet = splitConstraints1(constraints, condition, extras);
  for (auto c : tmpSet) {
    if (std::find(split.begin(), split.end(), c) == split.end()) {
      split.push_back(c);
    } 
  }
  return split;
}

ConstraintSet FuzzingSolver::splitConstraints1(const ConstraintSet& constraints, ref<Expr> condition, 
                                  std::vector<const Array*> &extras) {
  ConstraintSet cs;
  Worklist worklist;
  std::vector<const Array*> arrays;
  findSymbolicObjects(condition, arrays);

  for (auto array : arrays) {
    worklist.insert(new SymbolicExpr(array));
  }
  while (!worklist.empty()) {
    auto fetched = worklist.remove();
    ConstraintSet tmpSet = fetch(fetched, worklist, constraints, extras);
    for (auto expr : tmpSet) {
      cs.push_back(expr);
    }
  }

  if (RecolossusDebugLog) {
    klee_warning("splitConstraints1: The whole fetched constraints are");
    ExprPPrinter::printConstraints(llvm::errs(), cs);
  }

  return cs;
}

ConstraintSet FuzzingSolver::fetch(ref<Expr> fetched, Worklist& worklist, const ConstraintSet& constraints,
                                  std::vector<const Array*> &extras) {
  ConstraintSet cs;

  switch (fetched->getKind()) {
    default: assert(0 && "FIXME: Unhandled Expr");
    case Expr::Constant: {
      ref<ConstantExpr> ce = cast<ConstantExpr>(fetched);
      // Track the symbolic object if the argument is valid.
      // Fetch the pointee and add it to the worklist with constraints.
      // The readOnly attribute of op.second prevents tracking of constant pointees.
      // For instance, in strcmp(str[0], 'e'), where str length is 2 and 'e' has address addr_e,
      // only the contents of str[0] and str[1] are tracked, not 'e'.
      if (ObjectPair op;
          ce->getWidth() == Context::get().getPointerWidth() &&
          addressSpace->resolveOne(ce, op)  && !op.second->readOnly) {
          auto objectState = op.second;
          auto allBytes = objectState->getAllBytes();
          for (auto bytes : allBytes) {
            if (bytes->getKind() != Expr::Read) continue;
            auto pointee = cast<ReadExpr>(bytes)->updates.root;
            extras.push_back(pointee);
            ref<SymbolicExpr> symBytes(new SymbolicExpr(pointee));
            auto tmpSet = fetch(symBytes, worklist, constraints, extras);
            for (auto tmp : tmpSet) {
              cs.push_back(tmp);
            }
          }
      } 
    } break;
    case Expr::Symbolic: {
      // Lookup the constraints related to se
      auto symbolic = cast<SymbolicExpr>(fetched);
      // Add related constraints
      for (auto constraint : constraints) {
        std::vector<const Array*> arrays;
        findSymbolicObjects(constraint, arrays);

        // 1. ExtOpExpr Constraints
        if (constraint->getKind() == Expr::Eq) {
          ref<EqExpr> eq = cast<EqExpr>(constraint);
          if (eq->right->getKind() == Expr::ExtOp) {
            // if c is of type (Eq rv (ExtOp(arg1, arg2, ..)))
            //  then worklist.push(rv, arg1, arg2, ..);
            // 1. Deal with normal symbolic (Read, Concat, SExt and more)
            // Check for 
            if (containSymbolicArg(eq, symbolic)) {
              cs.push_back(constraint);
              // Update worklist: add pointer if necessary
              ref<ExtOpExpr> extOp = cast<ExtOpExpr>(eq->right);
              for (auto arg : extOp->getArgs()) {
                if (arg->getKind() == Expr::Constant) {
                  worklist.insert(arg);
                }
              }
              // Update worklist: add normal symbolic variables (return value included)
              for (auto a : arrays) {
                worklist.insert(new SymbolicExpr(a));
              }
            }
            continue;
          }
        }
        // 2. Non ExtOpExpr
        if (std::find(arrays.begin(), arrays.end(), symbolic->array) != arrays.end()) {
          cs.push_back(constraint);
          for (auto a : arrays) {
            worklist.insert(new SymbolicExpr(a));
          }
          // FIXME: Deal with pointers?
        }
      }
    } break;
    #undef FILTER
  }
  return cs;
}

bool FuzzingSolver::containSymbolicArg(const ref<EqExpr> eq, const ref<SymbolicExpr> symbolic) {
  assert(eq->right->getKind() == Expr::ExtOp && "FIXME: Unhandled Expr");
  // 1. Not pointer type
  std::vector<const Array*> arrays;
  findSymbolicObjects(eq, arrays); 
  if (find(arrays.begin(), arrays.end(), symbolic->array) != arrays.end()) {
    return true;
  }
  auto extOp = cast<ExtOpExpr>(eq->right);

  // 2. Maybe pointer type
  for (auto arg : extOp->getArgs()) {
    if (arg->getKind() == Expr::Constant) {
      auto ce = cast<ConstantExpr>(arg);
      // CB Functions holding pointer type
      if (ObjectPair op; ce->getWidth() == Context::get().getPointerWidth() &&
        addressSpace->resolveOne(ce, op)  && !op.second->readOnly) {
        auto allBytes = op.second->getAllBytes();
        for (auto bytes : allBytes) {
          std::vector<const Array*> arrays;
          findSymbolicObjects(bytes, arrays);
          if (find(arrays.begin(), arrays.end(), symbolic->array) != arrays.end()) {
            // symbolic is pointed by current pointer ce
            return true;
          }
        }
      }
    }
  }
  return false;
}

static bool containsExtOp(const ref<Expr> e) {
  if (e->getKind() == Expr::Kind::Eq) {
    const EqExpr* ee = cast<EqExpr>(e);
    if (ee->right->getKind() == Expr::Kind::ExtOp) {
      return true;
    }
  }
  return false;
}

llvm::Optional<Assignment> FuzzingSolver::getFeasibleAssignment(
  const ConstraintSet &constraints, ref<Expr> expr, std::string locInfo) {
    // predictor
    if (predictor->lookupState(locInfo) == ST_UNKNOWN) {
      return llvm::None;
    }
    if (RecolossusDebugLog) {
      klee_warning("DEBUG: Invoking KRPK getFeasibleAssignmemt");
    }
    // Fast Path: Skip fuzzing if the counter-example of expr is in the constraints.
    for (const auto& c: constraints) {
      ref<Expr> cex = Expr::createIsZero(expr);
      if (cex == c) {
        return llvm::None;
      }
    }

    std::vector<const Array*> extras;
    ConstraintSet split = splitConstraints(constraints, expr, extras);

    // Fast Path: Skip unnecessary fuzzing when no extop is present.
    bool shouldFuzz = false;
    for (const auto& c: split) {
      if (containsExtOp(c)) {
        shouldFuzz = true;
        break;
      }
    }
    shouldFuzz = shouldFuzz || containsExtOp(expr);
    if (!shouldFuzz) {
      return llvm::None;
    }

    if (RecolossusDebugLog) {
      klee_warning("Before splitting query is:");
      ExprPPrinter::printQuery(llvm::errs(), constraints,  expr);
      klee_warning("After splitting query is:");
      ExprPPrinter::printQuery(llvm::errs(), split,  expr);
    }

    if (split.empty()) {
      return llvm::None;
    }

    std::vector<std::vector<unsigned char> > values;
    std::vector<const Array*> objects;
    for (auto c : split) {
      findSymbolicObjects(c, objects);
    }
    for (auto arr : extras) {
      std::vector<const Array*> tmp = objects;
      if (std::find(tmp.begin(), tmp.end(), arr) == tmp.end()) {
        objects.push_back(arr);
      }
    }

    bool success = solver->getInitialValues(Query(split, expr), objects, values);

    std::string head = "DEBUG: FUZZ result: " + locInfo;
    std::string query_str;
    llvm::raw_string_ostream output(query_str);
    ExprPPrinter::printQuery(output, split, expr);
    output.flush();
    head = head + (success ? " SAT: Find a new path!" : " Unknown");
    klee_warning("%s", head.c_str());
    // klee_warning("%s\n", query_str.c_str());

    predictor->setState(locInfo, success);
    if (!success) {
        return llvm::None;
    }
    return Assignment(objects, values);
}

void FuzzingSolver::setAddressSpace(const AddressSpace* addressSpace) {
    assert(addressSpace != nullptr && "Error when setAddressSpace!");
    this->addressSpace = addressSpace; 
    ((KRPKSolver*)coreKRPKSolver.get())->setAddressSpace(addressSpace);
}
