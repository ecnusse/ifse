//===-- FilteringSolver.cpp - Wraper solver ---------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include "klee/Core/Interpreter.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Expr/SymcreteAndExtOpFilter.h"
#include "klee/Solver/Solver.h"
#include "klee/Solver/FilteringSolver.h"

#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Solver/IncompleteSolver.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <cassert>
#include <memory>
#include <unordered_map>
#include <utility>

using namespace klee;

ConstraintSet FilteringSolver::filterConstraints(const ConstraintSet &cs) {
    ConstraintSet constaints;
    SymcreteAndExtOpFilter replacer;

    // Deferred Concretization
    // 1. All terms that contain external operations are dropped
    for (auto c: cs) {
      constaints.push_back(replacer.visit(c));
    }
    // 2. All symcrete values ⟨αi ,ci ⟩ are replaced by their concrete values ci
    if (symcreteMap && !symcreteMap->empty()) {
      for (auto p: *symcreteMap) {
        auto array = p.second.first;
        auto concrete = p.second.second;
        for (size_t i = 0; i < concrete.size(); i++) {
          auto offset = ConstantExpr::create(i, Expr::Int32);
          UpdateList ul(array, nullptr);
          // create a readExpr representing reading updatenode with index offset from updatelist ul
          auto read = ReadExpr::create(ul, offset);
          auto value = ConstantExpr::create(concrete[i], Expr::Int8);
          // create a equalExpr representing that the reading from updatelist[offset] equals concrete[offset]
          auto eq = EqExpr::create(read, value); 
          constaints.push_back(eq);
        }
      }
    }
    return constaints;
}

ref<Expr> FilteringSolver::filterExpr(ref<Expr> expr) {
    SymcreteAndExtOpFilter replacer;
    auto newExpr = replacer.visit(expr);
    return newExpr;
}

std::pair<ConstraintSet, ref<Expr>> FilteringSolver::filterQuery(const Query &query) {
    if (!symcreteMap || symcreteMap->empty()) {
      return std::make_pair(query.constraints, query.expr);
    }
    auto constraints = filterConstraints(query.constraints);
    auto expression = filterExpr(query.expr);
    return std::make_pair(constraints, expression);
}

void FilteringSolver::setSymcreteMap(std::shared_ptr<std::map<std::string, bindings_ty>> symcreteMap) {
  assert(symcreteMap && "NULL pointer.");
  this->symcreteMap = symcreteMap;
  klee::setSymcreteMapSingleton(symcreteMap);
}

void FilteringSolver::clearSymcreteMap() {
  this->symcreteMap = nullptr;
  klee::clearSymcreteMapSingleton();
}

bool FilteringSolver::computeValidity(const Query &query, Solver::Validity &result) {
  auto pair = filterQuery(query);
  auto newQuery = Query(pair.first, pair.second);
  return solver->impl->computeValidity(newQuery, result);
}

bool FilteringSolver::computeTruth(const Query &query, bool &isValid) {
  auto pair = filterQuery(query);
  auto newQuery = Query(pair.first, pair.second);
  return solver->impl->computeTruth(newQuery, isValid);
}

bool FilteringSolver::computeValue(const Query &query, ref<Expr> &result) {
  auto pair = filterQuery(query);
  auto newQuery = Query(pair.first, pair.second);
  return solver->impl->computeValue(newQuery, result);
}

bool FilteringSolver::computeInitialValues(const Query& query,
                          const std::vector<const Array*> &objects,
                          std::vector< std::vector<unsigned char> > &values,
                          bool &hasSolution) {
  auto pair = filterQuery(query);
  auto newQuery = Query(pair.first, pair.second);
  return solver->impl->computeInitialValues(newQuery, objects, values, hasSolution);
}

SolverImpl::SolverRunStatus FilteringSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

void FilteringSolver::setCoreSolverTimeout(time::Span timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}


char *FilteringSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

///

std::unique_ptr<Solver>
klee::createFilteringSolver(std::unique_ptr<Solver> solver) {
  return std::make_unique<Solver>(
      std::make_unique<FilteringSolver>(std::move(solver)));
}
