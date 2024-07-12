//===-- FuzzingSolver.h ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_FUZZINGSOLVER_H
#define KLEE_FUZZINGSOLVER_H

#include "AddressSpace.h"
#include "../lib/Solver/KRPKSolver.h"
#include "klee/ADT/Ref.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Solver/Solver.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/System/Time.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/Optional.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <functional>
#include <map>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

namespace klee {
class ConstraintSet;
class Solver;

/// FuzzingSolver - A simple class which wraps a solver 
///   and handles external operations
class FuzzingSolver {
private:
  struct APIntHash {
      std::size_t operator()(const llvm::APInt& val) const {
          return llvm::hash_value(val);
      }
  };

  struct ExprHash {
      std::size_t operator()(const ref<Expr> expr) const {
        if (expr->getKind() == Expr::Symbolic) {
          return std::hash<std::string>()(cast<SymbolicExpr>(expr)->array->getName());
        } else if (expr->getKind() == Expr::Constant) {
          return APIntHash()(cast<ConstantExpr>(expr)->getAPValue());
        } else assert(0 && "FIXME: Unhandled Expression");
      }
  };

  struct ExprEqual {
    bool operator()(const ref<Expr> lhs, const ref<Expr> rhs) const {
        if (lhs->getKind() != rhs->getKind()) {
          return false;
        }
        if (lhs->getKind() == Expr::Constant) {
          return cast<ConstantExpr>(lhs)->getAPValue() 
                == cast<ConstantExpr>(rhs)->getAPValue();
        } else if (lhs->getKind() == Expr::Symbolic) {
          return cast<SymbolicExpr>(lhs)->array->getName() 
                == cast<SymbolicExpr>(rhs)->array->getName();
        } else assert(0 && "FIXME: Unhandled Expression");
    }
  };

  static void printSymbolic(ref<Expr> expr) {
    if (expr->getKind() == Expr::Symbolic) {
      auto tmpFetched = cast<SymbolicExpr>(expr);
      klee_warning( "DEBUG: %s", tmpFetched->array->name.c_str());
    } else if (expr->getKind() == Expr::Constant) {
      ExprPPrinter::printOne(llvm::errs(), "DEBUG:", expr);
    }
  }

  class Worklist {
    private:
      std::vector<ref<Expr>> vec;
      std::unordered_set<ref<Expr>, ExprHash, ExprEqual> set;
    public:
      bool empty() { return vec.empty(); }

      void insert(const ref<Expr> r) {
        if (set.find(r) == set.end()) {
            vec.push_back(r);
            set.insert(r);
        }
      }

      ref<Expr> remove() {
        ref<Expr> removedItem = nullptr;
        if (!vec.empty()) {
          removedItem = vec.front();
          vec.erase(vec.begin());
        }
        return removedItem;
      }
  };

  enum State {
    WE_SAT,
    ST_SAT,
    WE_UNKNOWN,
    ST_UNKNOWN,
  };
  class Predictor {
    // string -> STATE
    std::map<std::string, State> map;
    public:

    State lookupState(std::string locInfo) {
      auto it = map.find(locInfo);
      if (it != map.end()) {
        return it->second;
      } else {
        map.insert({locInfo, WE_SAT});
        return WE_SAT;
      }
    }

    void setState(std::string locInfo, bool success) {
      auto it = map.find(locInfo);
      switch (it->second) {
      case WE_SAT: {
        if (!success) it->second = ST_SAT;
      } break;
      case ST_SAT: {
        if (!success) it->second = WE_UNKNOWN;
        else it->second = WE_SAT;
      } break;
      case WE_UNKNOWN: {
        if (!success) it->second = ST_UNKNOWN;
        else it->second = ST_SAT;
      } break;
      case ST_UNKNOWN: break;
      }
    }
  };

  const AddressSpace* addressSpace;
  std::unique_ptr<Predictor> predictor;
public:
  std::unique_ptr<Solver> solver;
  std::shared_ptr<Solver> coreKRPKSolver;
public:
  /// FuzzingSolver- Construct a new fuzzing solver.
  FuzzingSolver(std::shared_ptr<Solver> solver) : coreKRPKSolver(solver) {
    predictor = std::make_unique<Predictor>();
  }

  void setSolver(std::unique_ptr<Solver> solver) { this->solver = std::move(solver); }

  void setTimeout(time::Span t) { solver->setCoreSolverTimeout(t); }

  char *getConstraintLog(const Query &query) {
    return solver->getConstraintLog(query);
  }

  bool mustBeTrue(const ConstraintSet &, ref<Expr>, bool &result,
                  SolverQueryMetaData &metaData);

  bool mustBeFalse(const ConstraintSet &, ref<Expr>, bool &result,
                   SolverQueryMetaData &metaData);

  bool mayBeTrue(const ConstraintSet &, ref<Expr>, bool &result,
                 SolverQueryMetaData &metaData);

  bool mayBeFalse(const ConstraintSet &, ref<Expr>, bool &result,
                  SolverQueryMetaData &metaData);

  bool getValue(const ConstraintSet &, ref<Expr> expr,
                ref<ConstantExpr> &result, SolverQueryMetaData &metaData);

  bool getInitialValues(const ConstraintSet &,
                        const std::vector<const Array *> &objects,
                        std::vector<std::vector<unsigned char>> &result,
                        SolverQueryMetaData &metaData);

  llvm::Optional<Assignment> getFeasibleAssignment(
    const ConstraintSet &constraints, ref<Expr> expr, std::string locInfo);

  std::pair<ref<Expr>, ref<Expr>> getRange(const ConstraintSet &,
                                           ref<Expr> query,
                                           SolverQueryMetaData &metaData);
  void setAddressSpace(const AddressSpace* addressSpace);

  ConstraintSet splitConstraints1(const ConstraintSet& constraints,
                                  ref<Expr> symcrete,
                                  std::vector<const Array*> &extras);

  ConstraintSet splitConstraints(const ConstraintSet& constraints,
                                ref<Expr> conditon,
                                std::vector<const Array*> &extras);

  ConstraintSet fetch(ref<Expr> fetched,
                      Worklist& worklist,
                      const ConstraintSet& constraints,
                      std::vector<const Array*> &extras);

  bool containSymbolicArg(const ref<EqExpr> extOp, const ref<SymbolicExpr> symbolic);
};
}

#endif /* KLEE_FUZZINGSOLVER_H */
