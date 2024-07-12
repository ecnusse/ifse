//===-- FilteringSolver.cpp - Wraper solver ---------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include "klee/ADT/Ref.h"
#include "klee/Core/Interpreter.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Solver/Solver.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Solver/IncompleteSolver.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"

#include <cassert>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>

using namespace klee;

class FilteringSolver : public SolverImpl {
private:
  // ExecutionState *currentState;
  std::unique_ptr<Solver> solver;

  typedef std::pair<const Array*, std::vector<unsigned char>> bindings_ty;
  std::shared_ptr<std::map<std::string, bindings_ty>> symcreteMap;

public:
  FilteringSolver(std::unique_ptr<Solver> solver) : solver(std::move(solver)), symcreteMap(nullptr) {}

  void setSymcreteMap(std::shared_ptr<std::map<std::string, bindings_ty>> symcreteMap);
  void clearSymcreteMap();

  ConstraintSet filterConstraints(const ConstraintSet &cs);
  ref<Expr> filterExpr(ref<Expr> expr);
  std::pair<ConstraintSet, ref<Expr>> filterQuery(const Query &query);

  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeTruth(const Query&, bool &isValid);
  bool computeValue(const Query& query, ref<Expr> &result);
  bool computeInitialValues(const Query& query,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution); 
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query&);
  void setCoreSolverTimeout(time::Span timeout);
};