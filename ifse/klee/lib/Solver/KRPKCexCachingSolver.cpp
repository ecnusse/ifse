//===-- KRPKKRPKCexCachingSolver.cpp ----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver/Solver.h"

#include "klee/ADT/MapOfSets.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Expr/ExprVisitor.h"
#include "klee/Support/OptionCategories.h"
#include "klee/Statistics/TimerStatIncrementer.h"
#include "klee/Solver/SolverImpl.h"
#include "klee/Solver/SolverStats.h"
#include "klee/Support/ErrorHandling.h"

#include "llvm/Support/CommandLine.h"

#include <cassert>
#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

using namespace klee;
using namespace llvm;

namespace {
cl::opt<bool> DebugKRPKCexCacheCheckBinding(
    "krpk-debug-cex-cache-check-binding", cl::init(false),
    cl::desc("Debug the correctness of the counterexample "
             "cache assignments (default=false)"),
    cl::cat(SolvingCat));

cl::opt<bool>
    KRPKCexCacheTryAll("krpk-cex-cache-try-all", cl::init(false),
                   cl::desc("Try substituting all counterexamples before "
                            "asking the SMT solver (default=false)"),
                   cl::cat(SolvingCat));

cl::opt<bool>
    KRPKCexCacheSuperSet("krpk-cex-cache-superset", cl::init(false),
                     cl::desc("Try substituting SAT superset counterexample "
                              "before asking the SMT solver (default=false)"),
                     cl::cat(SolvingCat));

cl::opt<bool> KRPKCexCacheExperimental(
    "krpk-cex-cache-exp", cl::init(false),
    cl::desc("Optimization for validity queries (default=false)"),
    cl::cat(SolvingCat));

} // namespace

///

typedef std::set< ref<Expr> > KeyType;

struct AssignmentLessThan {
  bool operator()(const Assignment *a, const Assignment *b) const {
    return a->bindings < b->bindings;
  }
};


class KRPKCexCachingSolver : public SolverImpl {
  typedef std::set<Assignment*, AssignmentLessThan> assignmentsTable_ty;

  std::unique_ptr<Solver> solver;
  
  MapOfSets<ref<Expr>, Assignment*> cache;
  // memo table
  assignmentsTable_ty assignmentsTable;

  bool searchForAssignment(KeyType &key, 
                           Assignment *&result);
  
  bool lookupAssignment(const Query& query, KeyType &key, Assignment *&result);

  bool lookupAssignment(const Query& query, Assignment *&result) {
    KeyType key;
    return lookupAssignment(query, key, result);
  }

  bool getAssignment(const Query& query, Assignment *&result, const std::vector<const Array*> &objects);
  
public:
  KRPKCexCachingSolver(std::unique_ptr<Solver> solver)
      : solver(std::move(solver)) {}
  ~KRPKCexCachingSolver();
  
  bool computeTruth(const Query&, bool &isValid);
  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeValue(const Query&, ref<Expr> &result);
  bool computeInitialValues(const Query&,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query& query);
  void setCoreSolverTimeout(time::Span timeout);
};

///

struct NullAssignment {
  bool operator()(Assignment *a) const { return !a; }
};

struct NonNullAssignment {
  bool operator()(Assignment *a) const { return a!=0; }
};

struct NullOrSatisfyingAssignment {
  KeyType &key;
  
  NullOrSatisfyingAssignment(KeyType &_key) : key(_key) {}

  bool operator()(Assignment *a) const { 
    return !a || a->satisfies(key.begin(), key.end()); 
  }
};

/// searchForAssignment - Look for a cached solution for a query.
///
/// \param key - The query to look up.
/// \param result [out] - The cached result, if the lookup is successful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return - True if a cached result was found.
bool KRPKCexCachingSolver::searchForAssignment(KeyType &key, Assignment *&result) {
  Assignment * const *lookup = cache.lookup(key);
  if (lookup) {
    result = *lookup;
    return true;
  }

  if (KRPKCexCacheTryAll) {
    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = 0;
    if (KRPKCexCacheSuperSet)
      lookup = cache.findSuperset(key, NonNullAssignment());

    // Otherwise, look for a subset which is unsatisfiable, see below.
    if (!lookup) 
      lookup = cache.findSubset(key, NullAssignment());

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }

    // Otherwise, iterate through the set of current assignments to see if one
    // of them satisfies the query.
    for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
           ie = assignmentsTable.end(); it != ie; ++it) {
      Assignment *a = *it;
      if (a->satisfies(key.begin(), key.end())) {
        result = a;
        return true;
      }
    }
  } else {
    // FIXME: Which order? one is sure to be better.

    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = 0;
    if (KRPKCexCacheSuperSet)
      lookup = cache.findSuperset(key, NonNullAssignment());

    // Otherwise, look for a subset which is unsatisfiable -- if the subset is
    // unsatisfiable then no additional constraints can produce a valid
    // assignment. While searching subsets, we also explicitly the solutions for
    // satisfiable subsets to see if they solve the current query and return
    // them if so. This is cheap and frequently succeeds.
    if (!lookup) 
      lookup = cache.findSubset(key, NullOrSatisfyingAssignment(key));

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }
  }
  
  return false;
}

/// lookupAssignment - Lookup a cached result for the given \arg query.
///
/// \param query - The query to lookup.
/// \param key [out] - On return, the key constructed for the query.
/// \param result [out] - The cached result, if the lookup is successful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return True if a cached result was found.
bool KRPKCexCachingSolver::lookupAssignment(const Query &query, 
                                        KeyType &key,
                                        Assignment *&result) {
  key = KeyType(query.constraints.begin(), query.constraints.end());
  ref<Expr> neg = Expr::createIsZero(query.expr);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(neg)) {
    if (CE->isFalse()) {
      result = (Assignment*) 0;
      ++stats::queryCexCacheHits;
      return true;
    }
  } else {
    key.insert(neg);
  }

  bool found = searchForAssignment(key, result);
  if (found)
    ++stats::queryCexCacheHits;
  else ++stats::queryCexCacheMisses;
    
  return found;
}

bool KRPKCexCachingSolver::getAssignment(const Query& query,
                                     Assignment *&result,
                                     const std::vector<const Array*> &objects) {
  KeyType key;
  if (lookupAssignment(query, key, result))
    return true;

  std::vector< std::vector<unsigned char> > values;
  bool hasSolution;
  if (!solver->impl->computeInitialValues(query, objects, values, 
                                          hasSolution))
    return false;
    
  Assignment *binding;
  if (hasSolution) {
    binding = new Assignment(objects, values);

    // Memoize the result.
    std::pair<assignmentsTable_ty::iterator, bool>
      res = assignmentsTable.insert(binding);
    if (!res.second) {
      delete binding;
      binding = *res.first;
    }
    
    if (DebugKRPKCexCacheCheckBinding)
      if (!binding->satisfies(key.begin(), key.end())) {
        query.dump();
        binding->dump();
        klee_error("Generated assignment doesn't match query");
      }
  } else {
    binding = (Assignment*) 0;
  }
  
  result = binding;
  cache.insert(key, binding);

  return true;
}

///

KRPKCexCachingSolver::~KRPKCexCachingSolver() {
  cache.clear();
  for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
         ie = assignmentsTable.end(); it != ie; ++it)
    delete *it;
}

bool KRPKCexCachingSolver::computeValidity(const Query& query,
                                       Solver::Validity &result) {
  assert(0 && "Unimplemented KRPKKRPKCexCachingSolver API");
}

bool KRPKCexCachingSolver::computeTruth(const Query& query,
                                    bool &isValid) {
  assert(0 && "Unimplemented KRPKKRPKCexCachingSolver API");
}

bool KRPKCexCachingSolver::computeValue(const Query& query,
                                    ref<Expr> &result) {
  assert(0 && "Unimplemented KRPKKRPKCexCachingSolver API");
}

bool 
KRPKCexCachingSolver::computeInitialValues(const Query& query,
                                       const std::vector<const Array*> 
                                         &objects,
                                       std::vector< std::vector<unsigned char> >
                                         &values,
                                       bool &hasSolution) {
  KeyType key = KeyType(query.constraints.begin(), query.constraints.end());
  key.insert(query.expr);

  Assignment* const *lookup = cache.findSubset(key, NullAssignment());
  if (lookup) {
    assert(nullptr == (*lookup));
    hasSolution = false;
    return true; 
  }

  lookup = cache.findSuperset(key, NonNullAssignment());
  if (lookup) {
    Assignment* cached = *lookup;
    assert(nullptr != cached);
    hasSolution = true;
    assert(values.empty());
    for (size_t i = 0; i < objects.size(); i++) {
      std::vector<unsigned char> v = cached->bindings[objects[i]];
      values.push_back(v);
    }
    return true;
  }

  bool success = solver->impl->computeInitialValues(query, objects, values, hasSolution);
  
  if (success) {
    assert(hasSolution);
    cache.insert(key, new Assignment(objects, values));
    return true;
  }

  hasSolution = false;
  cache.insert(key, nullptr); // Unknown
  return true;
}

SolverImpl::SolverRunStatus KRPKCexCachingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *KRPKCexCachingSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void KRPKCexCachingSolver::setCoreSolverTimeout(time::Span timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///

std::unique_ptr<Solver>
klee::createKRPKCexCachingSolver(std::unique_ptr<Solver> solver) {
  return std::make_unique<Solver>(
      std::make_unique<KRPKCexCachingSolver>(std::move(solver)));
}
