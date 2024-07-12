#ifndef KLEE_KRPKSOLVER_H
#define KLEE_KRPKSOLVER_H

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <mutex>
#include <string>
#include <sys/types.h>
#include <vector>
#include "../lib/Core/ExecutionState.h"
#include "KRPKBuilder.h"
#include "../lib/Core/AddressSpace.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/System/Time.h"
#include "klee/Expr/ArrayCache.h"
#include "llvm/ADT/Optional.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "klee/Solver/Solver.h"
namespace klee {
/// KRPKSolver - A complete solver based on fuzzing
class KRPKSolver : public Solver {
public:
  /// KRPKSolver - Construct a new KRPKSolver.
  KRPKSolver();

  /// Get the query in SMT-LIBv2 format.
  /// \return A C-style string. The caller is responsible for freeing this.
  virtual char *getConstraintLog(const Query &);

  /// setCoreSolverTimeout - Set constraint solver timeout delay to the given
  /// value; 0
  /// is off.
  virtual void setCoreSolverTimeout(time::Span timeout);

  void setAddressSpace(const AddressSpace* addressSpace);
  void constructAndPrintSMT(const Query &query);
};
}

#endif
