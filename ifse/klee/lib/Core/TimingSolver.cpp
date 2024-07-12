//===-- TimingSolver.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "TimingSolver.h"

#include "ExecutionState.h"

#include "klee/ADT/Ref.h"
#include "klee/Config/Version.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Statistics/Statistics.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Expr/SymcreteAndExtOpFilter.h"
#include "klee/Expr/ExprUtil.h"

#include "CoreStats.h"
#include "klee/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

using namespace klee;
using namespace llvm;


bool TimingSolver::evaluate(const ConstraintSet &constraints, ref<Expr> expr,
                            Solver::Validity &result,
                            SolverQueryMetaData &metaData) {
  if (RecolossusDebugLog) {
    klee_warning("DEBUG: Using TimingSolver's evaluate, and query is as below");
    ExprPPrinter::printQuery(llvm::errs(), constraints, expr);
  }

  ++stats::queries;
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? Solver::True : Solver::False;
    return true;
  }

  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs) {
    expr = ConstraintManager::simplifyExpr(constraints, expr);
  }
  bool success = solver->evaluate(Query(constraints, expr), result);
  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::mustBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  ++stats::queries;
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE->isTrue() ? true : false;
    return true;
  }

  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);

  bool success = solver->mustBeTrue(Query(constraints, expr), result);
  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::mustBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                               bool &result, SolverQueryMetaData &metaData) {
  return mustBeTrue(constraints, Expr::createIsZero(expr), result, metaData);
}

bool TimingSolver::mayBeTrue(const ConstraintSet &constraints, ref<Expr> expr,
                             bool &result, SolverQueryMetaData &metaData) {
  bool res;
  if (!mustBeFalse(constraints, expr, res, metaData)) 
    return false;
  result = !res;
  return true;
}

bool TimingSolver::mayBeFalse(const ConstraintSet &constraints, ref<Expr> expr,
                              bool &result, SolverQueryMetaData &metaData) {
  bool res;
  if (!mustBeTrue(constraints, expr, res, metaData))
    return false;
  result = !res;
  return true;
}

bool TimingSolver::getValue(const ConstraintSet &constraints, ref<Expr> expr,
                            ref<ConstantExpr> &result,
                            SolverQueryMetaData &metaData) {
  ++stats::queries;
  // Fast path, to avoid timer and OS overhead.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(expr)) {
    result = CE;
    return true;
  }
  
  TimerStatIncrementer timer(stats::solverTime);

  if (simplifyExprs)
    expr = ConstraintManager::simplifyExpr(constraints, expr);

  bool success = solver->getValue(Query(constraints, expr), result);
  metaData.queryCost += timer.delta();

  return success;
}

bool TimingSolver::getInitialValues(
    const ConstraintSet &constraints, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char>> &result,
    SolverQueryMetaData &metaData) {
  ++stats::queries;
  if (objects.empty())
    return true;

  TimerStatIncrementer timer(stats::solverTime);

  bool success = solver->getInitialValues(
      Query(constraints, ConstantExpr::alloc(0, Expr::Bool)), objects, result);

  metaData.queryCost += timer.delta();

  return success;
}

llvm::Optional<std::pair<Assignment, ref<ConstantExpr>>> TimingSolver::getValueAndSolution (
  const ConstraintSet &constraints, ref<Expr> expr, SolverQueryMetaData &metaData) {

  std::vector<std::vector<unsigned char> > values;
  std::vector<const Array*> objects;
  //find symbolic arrays referenced in query, storing them in objects
  findSymbolicObjects(expr, objects); 

  bool rv = getInitialValues(constraints, objects, values, metaData); //find concrete value for all array that is referenced by expr.
  if (!rv) {
      return llvm::None;
  }
  auto resultAssignment = Assignment(objects, values);

  ref<ConstantExpr> resultExpr = resultAssignment.evaluate(expr);
  return std::make_pair(resultAssignment, resultExpr);
}

std::pair<ref<Expr>, ref<Expr>>
TimingSolver::getRange(const ConstraintSet &constraints, ref<Expr> expr,
                       SolverQueryMetaData &metaData) {
  ++stats::queries;
  TimerStatIncrementer timer(stats::solverTime);
  auto result = solver->getRange(Query(constraints, expr));
  metaData.queryCost += timer.delta();
  return result;
}
