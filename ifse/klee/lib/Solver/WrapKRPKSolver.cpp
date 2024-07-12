//===-- WrapKRPKSolver.cpp - a solver used fot forwarding methods ---------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include "klee/Expr/ExprVisitor.h"
#include "klee/Solver/Solver.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Solver/IncompleteSolver.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Solver/SolverStats.h"

#include <memory>
#include <unordered_map>
#include <utility>

using namespace klee;

class WrapKRPKSolver: public SolverImpl {
private:
  std::shared_ptr<Solver> solver;
public:
  WrapKRPKSolver(std::shared_ptr<Solver> solver) : solver(solver) {}

  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeTruth(const Query&, bool &isValid);
  bool computeValue(const Query& query, ref<Expr> &result) {
    return solver->impl->computeValue(query, result);
  }
  bool computeInitialValues(const Query& query,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution) {
    return solver->impl->computeInitialValues(query, objects, values, 
                                              hasSolution);
  }
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query&);
  void setCoreSolverTimeout(time::Span timeout);
};

bool WrapKRPKSolver::computeValidity(const Query& query,
                                    Solver::Validity &result) {
  return solver->impl->computeValidity(query, result);
}

bool WrapKRPKSolver::computeTruth(const Query& query,
                                 bool &isValid) {
  return solver->impl->computeTruth(query, isValid);
}

SolverImpl::SolverRunStatus WrapKRPKSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *WrapKRPKSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void WrapKRPKSolver::setCoreSolverTimeout(time::Span timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///

std::unique_ptr<Solver>
klee::createWrapKRPKSolver(std::shared_ptr<Solver> solver) {
  return std::make_unique<Solver>(
      std::make_unique<WrapKRPKSolver>(solver));
}
