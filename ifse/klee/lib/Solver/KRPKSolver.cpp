#include "KRPKSolver.h"

#include "../lib/Core/Executor.h"
#include "KRPKBuilder.h"
#include "klee/Expr/Assignment.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <iomanip>
#include <sstream>
#include <string>
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Expr/ExprUtil.h"
#include "klee/Module/KInstruction.h"
#include "klee/Solver/Solver.h"
#include "krpk.h"
#include "klee/Support/ErrorHandling.h"

#include "klee/Solver/SolverImpl.h"



using namespace klee;

namespace klee {

class KRPKArrayExprHash : public ArrayExprHash<KRPKNode> {
private:
  friend class KRPKSolver;
public:
  KRPKArrayExprHash(){};
  virtual ~KRPKArrayExprHash() {}
  void clear() {
    _array_hash.clear();
    _update_node_hash.clear();
  }
};
class KRPKSolverImpl : public SolverImpl {
friend class KRPKContext;

private:
    std::unique_ptr<KRPKRawFuzzSolver> solver; 
    SolverRunStatus runStatusCode;
    time::Span timeout;
    KRPKArrayExprHash _arr_hash;
    KRPKContext ctx;

public:
    const AddressSpace* addressSpace = nullptr;
    KRPKSolverImpl();
    ~KRPKSolverImpl();

    ///these global maps are used to avoid redefinition of const, close-box function and ctype.
    std::unordered_map<std::string, KRPKNode >
      constant_array_map, cb_map, ctype_map;

    ///avoid overlapping alloc on address
    std::unordered_set<uint64_t>
      allocated_addr;
    // std::vector<std::pair<uint64_t, size_t>> addr_alloc_map;
    
    char *getConstraintLog(const Query &);

    ///set timeout for fuzzer
    void setCoreSolverTimeout(time::Span t) {
      uint64_t milliseconds = t.toMicroseconds() / 1000;
      solver->set_timeout(milliseconds);
    }

    bool computeTruth(const Query &, bool &isValid);
    bool computeValue(const Query &, ref<Expr> &result);
    bool computeInitialValues(const Query &,
                              const std::vector<const Array *> &objects,
                              std::vector<std::vector<unsigned char> > &values,
                              bool &hasSolution);
    SolverRunStatus getOperationStatusCode();

    ///set addressSpace to find object related pointer.
    void setAddressSpace(const AddressSpace* addressSpace) {
        assert(addressSpace != nullptr && "Error when setAddressSpace!");
        this->addressSpace = addressSpace;
    }
    /// construct each constraint of Query into a KRPKNode and return the vector of KRPKNode.
    void constructConstraintsFromQuery(const Query &query, std::vector<KRPKNode> &result);

    /// a wrapper of constructActual
    KRPKNode construct(ref<Expr> e, int *width_out);

    /// construct Expr e into KRPKNode
    KRPKNode constructActual(ref<Expr> e, int *width_out);

    /// extract from bit of expr
    KRPKNode bvBoolExtract(KRPKNode expr, int bit);

    /// extract from bottom to top of expr
    KRPKNode bvExtract(KRPKNode expr, unsigned top, unsigned bottom); 

    ///construct bitvec of 1
    KRPKNode bvOne(unsigned width);

    ///construct bitvec of 0
    KRPKNode bvZero(unsigned width);

    ///construct value of width into bitvec
    KRPKNode bvZExtConst(unsigned width, uint64_t value);

    /// parse KRPKmodel into assignment
    bool handleKRPKModel(const std::vector<const Array*>* objects, std::vector<std::vector<unsigned char>>* values, KRPKModel model);

    /// get Context of KRPKSolver
    KRPKContext getKRPKContext() {return ctx;}

    /// clear global maps to support clear environment when calling KRPK multiple times.
    void clearGlobalMap();
};

KRPKSolverImpl::KRPKSolverImpl() : runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
    // TODO: Current code only for test. Please implement this.
    this->solver = std::make_unique<KRPKRawFuzzSolver>();
    this->ctx = KRPKContext::default_();
}

KRPKSolverImpl::~KRPKSolverImpl() {
    // TODO: Current code only for test. Please implement this.
    constant_array_map.clear();
    cb_map.clear();
    ctype_map.clear();
    allocated_addr.clear();
}

KRPKSolver::KRPKSolver() : Solver(std::make_unique<KRPKSolverImpl>()) {}

char *KRPKSolver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void KRPKSolver::setCoreSolverTimeout(time::Span timeout) {
  impl->setCoreSolverTimeout(timeout);
}

void KRPKSolver::setAddressSpace(const AddressSpace* addressSpace) {
  auto krpkImpl = (KRPKSolverImpl*)impl.get();
  krpkImpl->setAddressSpace(addressSpace);
}

char *KRPKSolverImpl::getConstraintLog(const Query &query) {
  assert(0 && "Unimplemented KRPK API");
}

bool KRPKSolverImpl::computeTruth(const Query &query, bool &isValid) {
  assert(0 && "Unimplemented KRPK API");
}

bool KRPKSolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  assert(0 && "Unimplemented KRPK API");
}

bool KRPKSolverImpl::computeInitialValues(const Query &query,
                                      const std::vector<const Array *> &objects,
                                      std::vector<std::vector<unsigned char> > &values,
                                      bool &hasSolution) {
    std::vector<KRPKNode> result;
    clearGlobalMap();
    constructConstraintsFromQuery(query, result);
    for(auto term: result) {
      KRPKNode assertion = ctx.make_assertion(term);
    }

    auto solvingResult = solver->solve(ctx);
    if(solvingResult.is_sat()) {
        auto model = solvingResult.get_model();
        bool rv = handleKRPKModel(&objects, &values, model);
        hasSolution = rv;
        return rv;
    } else {
        hasSolution = false;
        return false;
    }
}

SolverImpl::SolverRunStatus KRPKSolverImpl::getOperationStatusCode() {
  return runStatusCode;
}

KRPKNode KRPKSolverImpl::construct(ref<Expr> e, int *width_out) {

  if (isa<ConstantExpr>(e)) {
    return constructActual(e, width_out);
  } else {
      int width;
      if (!width_out)
        width_out = &width;
      KRPKNode res = constructActual(e, width_out);
      return res;
  }
}

std::vector<uint8_t> uint64ToVector(uint64_t value) {
    std::vector<uint8_t> result;
    for (int i = 0; i < 8; i++) {
        result.push_back(static_cast<uint8_t>((value >> (i * 8)) & 0xFF));
    }
    return result;
}

std::vector<uint8_t> uint32ToVector(uint32_t value) {
    std::vector<uint8_t> result;
    for (int i = 0; i < 4; i++) {
        result.push_back(static_cast<uint8_t>((value >> (i * 8)) & 0xFF));
    }
    return result;
}

KRPKNode KRPKSolverImpl::bvOne(unsigned width) { return bvZExtConst(width, 1); }

KRPKNode KRPKSolverImpl::bvZero(unsigned width) { return bvZExtConst(width, 0); }

KRPKNode KRPKSolverImpl::bvBoolExtract(KRPKNode expr, int bit) {
  return KRPKNode::make_eq({KRPKNode::make_extract(bit, bit, expr), KRPKNode::make_bool2bv(KRPKNode::make_true())});
}


KRPKNode KRPKSolverImpl::bvZExtConst(unsigned width, uint64_t value) {
  if (width <= 64) {
    std::vector<uint8_t> bytes = uint64ToVector(value);
    return KRPKNode::make_bv_literal(bytes, width);
  }
  KRPKNode expr = KRPKNode::make_bv_literal(uint64ToVector(value), 64);
  return KRPKNode::make_zero_extend(width - 64, expr);
}

KRPKNode KRPKSolverImpl::constructActual(ref<Expr> e, int *width_out) {
  int width;
  if (!width_out)
    width_out = &width;

  ++stats::queryConstructs;

  switch (e->getKind()) {
  case Expr::Constant: {
    ConstantExpr *CE = cast<ConstantExpr>(e);
    *width_out = CE->getWidth();

    // Coerce to bool if necessary.
    if (*width_out == 1)
      return CE->isTrue() ? KRPKNode::make_true() : KRPKNode::make_false();

    // Fast path.
    if (*width_out <= 32) {
        //return bvConst32(*width_out, CE->getZExtValue(32));
        std::vector<uint8_t> bytes = uint32ToVector(CE->getZExtValue(32));
        return KRPKNode::make_bv_literal(bytes, *width_out);
    }
        
    if (*width_out <= 64) {
        std::vector<uint8_t> bytes = uint64ToVector(CE->getZExtValue());
        return KRPKNode::make_bv_literal(bytes, *width_out);
    }

    KRPKNode current = KRPKNode::make_bv_literal(uint64ToVector(CE->Extract(0, 64)->getZExtValue()), 64);
    
    for (unsigned int i = 1; i < CE->getWidth() / 64 + (CE->getWidth() % 64 == 0 ? 0 : 1); i++) {
      auto w = std::min(64U, CE->getWidth() - i * 64);
      auto bytes8 = KRPKNode::make_bv_literal(uint64ToVector(CE->Extract(i * 64, w) -> getZExtValue()), w);
      current = KRPKNode::make_concat(bytes8, current);
    }
    return current;
  }

  // Special
  case Expr::NotOptimized: {
    NotOptimizedExpr *noe = cast<NotOptimizedExpr>(e);
    return construct(noe->src, width_out);
  }

  case Expr::Read: {
    ReadExpr *re = cast<ReadExpr>(e);
    assert(re && re->updates.root);
    *width_out = re->updates.root->getRange();
    std::string name = re->updates.root->getName();
    auto range = re->updates.root->getRange();
    auto domain = re->updates.root->getDomain();
    KRPKNode index = construct(re->index, 0);

    auto find = constant_array_map.find(name); 
    if(find == constant_array_map.end()) {       
        KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
        KRPKNode range_index = KRPKNode::make_numeral_index(range);
        KRPKNode domain_index = KRPKNode::make_numeral_index(domain);
        KRPKNode range_sort = KRPKNode::make_simple_sort(sort_sym, {range_index});
        KRPKNode domain_sort = KRPKNode::make_simple_sort(sort_sym, {domain_index});
        KRPKNode array_sort_sym = KRPKNode::make_symbol("Array");
        KRPKNode array_sort = KRPKNode::make_parametric_sort(array_sort_sym, {}, {domain_sort, range_sort});

        KRPKNode constant;
        KRPKNode select;
        const Array* array = re->updates.root;
        if (array->isConstantArray()) {
          std::vector<uint8_t> default_bytes;
          for (unsigned i = 0; i < range / 8; i++) {
            default_bytes.push_back(0);
          }
          // 1. Make constant array
          //    For example: (as const (Array Int Int)) 
          constant = KRPKNode::make_array_const(array_sort, KRPKNode::make_bv_literal(default_bytes, range));

          // 2. Wrap const array with store statements
          //    For example: (store (store (store (as const (Array Int Int)) 0 0) 1 2) 2 4) 
          std::ostringstream ss;
          std::string prodived_bytes;
          for (unsigned long i = 0; i < array->constantValues.size(); i++) {
            ref<ConstantExpr> c = array->constantValues[i];
            auto value = c->getAPValue().getZExtValue();
            assert(value <= 255);
            ss << std::setw(2) << std::setfill('0') << std::hex << value;
            prodived_bytes += ss.str();
            ss.str("");
            ss.clear();
          }
          constant = KRPKNode::make_array_const_with_provided_values(array_sort, KRPKNode::make_bv_literal(default_bytes, range), prodived_bytes.c_str());
          select = KRPKNode::make_select(constant, index);
        } else {
          constant = ctx.declare_constant(name, array_sort);
          KRPKNode ensuredIndex = construct(ConstantExpr::alloc(re->updates.root->size - 1, re->updates.root->getDomain()), 0);
          auto ei = KRPKNode::make_ensure_index(KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})), ensuredIndex);
          std::vector<uint8_t> default_index;
          for (unsigned i = 0; i < domain / 8; i++) {
            default_index.push_back(0);
          }

          ctx.make_assertion(ei);

          select = KRPKNode::make_select(KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})), index); // ???
          constant_array_map.insert(std::make_pair(name, constant));
        }
        return select;
    } else {
      KRPKNode constant = find->second;
      KRPKNode select = KRPKNode::make_select(
        KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})),
        index);
      return select;
    }
  }

  //todo: conditional jump(ite)
  case Expr::Select: {
    SelectExpr *se = cast<SelectExpr>(e);
    KRPKNode cond = construct(se->cond, 0);
    KRPKNode tExpr = construct(se->trueExpr, width_out);
    KRPKNode fExpr = construct(se->falseExpr, width_out);
    KRPKNode ite = KRPKNode::make_ite(cond, tExpr, fExpr);
    return ite;
  }

  case Expr::Concat: {
    ConcatExpr *ce = cast<ConcatExpr>(e);
    unsigned numKids = ce->getNumKids();

    KRPKNode res = construct(ce->getKid(numKids - 1), 0);
    for (int i = numKids - 2; i >= 0; i--) {
      res = KRPKNode::make_concat(construct(ce->getKid(i), 0), res);
    }
    *width_out = ce->getWidth();
    return res;
  }

  case Expr::Extract: {
    ExtractExpr *ee = cast<ExtractExpr>(e);
    KRPKNode src = construct(ee->expr, width_out);
    *width_out = ee->getWidth();
    if (*width_out == 1) {
      return bvBoolExtract(src, ee->offset);
    } else {
      return KRPKNode::make_extract(ee->offset, ee->offset + *width_out - 1, src);
    }
  }

  // Casting

  case Expr::ZExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    KRPKNode src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    if(srcWidth == 1) {
      return KRPKNode::make_zero_extend(*width_out - 1, KRPKNode::make_bool2bv(src));
    } else {
      assert(*width_out > srcWidth && "Invalid width_out");
      return KRPKNode::make_zero_extend(*width_out - srcWidth, src);
    } 
    
  }


  case Expr::SExt: {
    int srcWidth;
    CastExpr *ce = cast<CastExpr>(e);
    KRPKNode src = construct(ce->src, &srcWidth);
    *width_out = ce->getWidth();
    assert(*width_out > srcWidth && "Invalid width_out");
    return KRPKNode::make_sign_extend(*width_out - srcWidth, src);
  }

  // Arithmetic
  case Expr::Add: {
    AddExpr *ae = cast<AddExpr>(e);
    KRPKNode left = construct(ae->left, width_out);
    KRPKNode right = construct(ae->right, width_out);
    assert(*width_out != 1 && "uncanonicalized add");
    KRPKNode result = KRPKNode::make_bvadd({left, right});
    return result;
  }

  case Expr::Sub: {
    SubExpr *se = cast<SubExpr>(e);
    KRPKNode left = construct(se->left, width_out);
    KRPKNode right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sub");
    KRPKNode result = KRPKNode::make_bvsub(left, right);
    return result;
  }

  case Expr::Mul: {
    MulExpr *me = cast<MulExpr>(e);
    KRPKNode right = construct(me->right, width_out);
    assert(*width_out != 1 && "uncanonicalized mul");
    KRPKNode left = construct(me->left, width_out);
    KRPKNode result = KRPKNode::make_bvmul({left, right});
    return result;
  }

  case Expr::UDiv: {
    UDivExpr *de = cast<UDivExpr>(e);
    KRPKNode left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized udiv");
    KRPKNode right = construct(de->right, width_out);
    KRPKNode result = KRPKNode::make_bvudiv(left, right);
    return result;
  }

  case Expr::SDiv: {
    SDivExpr *de = cast<SDivExpr>(e);
    KRPKNode left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized sdiv");
    KRPKNode right = construct(de->right, width_out);
    KRPKNode result = KRPKNode::make_bvsdiv(left, right);
    return result;
  }

  case Expr::URem: {
    URemExpr *de = cast<URemExpr>(e);
    KRPKNode left = construct(de->left, width_out);
    assert(*width_out != 1 && "uncanonicalized urem");

    KRPKNode right = construct(de->right, width_out);
    KRPKNode result =  KRPKNode::make_bvurem(left, right);
    return result;
  }

  case Expr::SRem: {
    SRemExpr *de = cast<SRemExpr>(e);
    KRPKNode left = construct(de->left, width_out);
    KRPKNode right = construct(de->right, width_out);
    assert(*width_out != 1 && "uncanonicalized srem");
    // LLVM's srem instruction says that the sign follows the dividend
    // (``left``).
    // Z3's C API says ``Z3_mk_bvsrem()`` does this so these seem to match.
    KRPKNode result =  KRPKNode::make_bvsrem(left, right);
    return result;
  }

  // Bitwise
  case Expr::Not: {
    NotExpr *ne = cast<NotExpr>(e);
    KRPKNode expr = construct(ne->expr, width_out);
    if (*width_out == 1) {
      return KRPKNode::make_not(expr);
    } else {
      return KRPKNode::make_bvnot(expr);
    }
  }

  case Expr::And: {
    AndExpr *ae = cast<AndExpr>(e);
    KRPKNode left = construct(ae->left, width_out);
    KRPKNode right = construct(ae->right, width_out);
    if (*width_out == 1) {
      return KRPKNode::make_and({left, right});
    } else {
      return KRPKNode::make_bvand({left, right});
    }
  }

  case Expr::Or: {
    OrExpr *oe = cast<OrExpr>(e);
    KRPKNode left = construct(oe->left, width_out);
    KRPKNode right = construct(oe->right, width_out);
    if (*width_out == 1) {
      return KRPKNode::make_or({left, right});
    } else {
      return KRPKNode::make_bvor({left, right});
    }
  }

  case Expr::Xor: {
    XorExpr *xe = cast<XorExpr>(e);
    KRPKNode left = construct(xe->left, width_out);
    KRPKNode right = construct(xe->right, width_out);

    if (*width_out == 1) {
      // XXX check for most efficient?
      return KRPKNode::make_xor({left, right});
      //return iteExpr(left, KRPKNode(notExpr(right)), right);
    } else {
      return KRPKNode::make_bvxor({left, right});
    }
  }

  case Expr::Shl: {
    ShlExpr *se = cast<ShlExpr>(e);
    KRPKNode left = construct(se->left, width_out);
    KRPKNode right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized shl");
    return KRPKNode::make_bvshl(left, right);
  }
  //may not be correct, to be checked 
  case Expr::LShr: {
    LShrExpr *lse = cast<LShrExpr>(e);
    KRPKNode left = construct(lse->left, width_out);
    KRPKNode right = construct(lse->right, width_out);
    assert(*width_out != 1 && "uncanonicalized lshr");
    return KRPKNode::make_bvlshr(left, right);
  }

  case Expr::AShr: {
    AShrExpr *ase = cast<AShrExpr>(e);
    KRPKNode left = construct(ase->left, width_out);
    KRPKNode right = construct(ase->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ashr");
    return KRPKNode::make_bvashr(left, right);
  }

  // Comparison

  case Expr::Eq: {
    EqExpr *ee = cast<EqExpr>(e);
    KRPKNode left = construct(ee->left, width_out);
    KRPKNode right = construct(ee->right, width_out);
    if (*width_out == 1) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(ee->left)) {
        if (CE->isTrue())
          return right;
        return KRPKNode::make_not(right);
      }
    }
    *width_out = 1;
    KRPKNode term = KRPKNode::make_eq({left, right});
    return term;
  }

  case Expr::Ult: {
    UltExpr *ue = cast<UltExpr>(e);
    KRPKNode left = construct(ue->left, width_out);
    KRPKNode right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ult");
    *width_out = 1;
    return KRPKNode::make_bvult(left, right);
  }

  case Expr::Ule: {
    UleExpr *ue = cast<UleExpr>(e);
    KRPKNode left = construct(ue->left, width_out);
    KRPKNode right = construct(ue->right, width_out);
    assert(*width_out != 1 && "uncanonicalized ule");
    *width_out = 1;
    return KRPKNode::make_bvule(left, right);
  }

  case Expr::Slt: {
    SltExpr *se = cast<SltExpr>(e);
    KRPKNode left = construct(se->left, width_out);
    KRPKNode right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized slt");
    *width_out = 1;
    return KRPKNode::make_bvslt(left, right);
  }

  case Expr::Sle: {
    SleExpr *se = cast<SleExpr>(e);
    KRPKNode left = construct(se->left, width_out);
    KRPKNode right = construct(se->right, width_out);
    assert(*width_out != 1 && "uncanonicalized sle");
    *width_out = 1;
    return KRPKNode::make_bvsle(left, right);
  }

// unused due to canonicalization
#if 0
  case Expr::Ne:
  case Expr::Ugt:
  case Expr::Uge:
  case Expr::Sgt:
  case Expr::Sge:
#endif

  case Expr::ExtOp: {
    ExtOpExpr *eoe = cast<ExtOpExpr>(e);
    llvm::Function* func = eoe->getFunc()->function;
    std::string funcName = (std::string)func->getName();

    std::vector<KRPKNode> args;
    std::vector<KRPKNode> argstype;
    KRPKNode returnType;
    args.reserve(eoe->getArgs().size());
    for (unsigned i = 0; i < eoe->getArgs().size(); i++) {
      auto a = eoe->getKid(i);
      auto paramType = func->getFunctionType()->getParamType(i); 
      std::string ctype_name = "";
      KRPKNode sort, ctype;
      if(paramType->isIntegerTy()) { //arg is int, sort is bitvec32 or bitvec64
        llvm::IntegerType* intType = llvm::cast<llvm::IntegerType>(paramType);
        unsigned width = intType->getBitWidth();
        if(width == 32) {
          ctype_name = "int";
        }else if(width == 64) {
          ctype_name = "long long";
        }
        else {
          assert(0 && "unsupported width!");
        }
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(a->getWidth())});
      } 
      else if(paramType->isPointerTy()) {//arg is pointer, sort is bitvec64
        assert(a->getWidth() == 64 && "width is not 64!");
        llvm::PointerType* ptrType = llvm::cast<llvm::PointerType>(paramType);
        llvm::Type* pointeeType = ptrType->getElementType();

        if (pointeeType == llvm::Type::getInt8Ty(ptrType->getContext())) { // The pointer is i8*
            ctype_name = "char *";
        } else if (pointeeType == llvm::Type::getInt16Ty(ptrType->getContext())) { // i16*
            ctype_name = "short *";
        } else if (pointeeType == llvm::Type::getInt32Ty(ptrType->getContext())) { // i32*
          ctype_name = "int *";
        } else if (pointeeType == llvm::Type::getInt64Ty(ptrType->getContext())) { // i64*
          ctype_name = "long long *";
        } else {
          assert(0 && "Not currently support");
        }

        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(64)});
        ConstantExpr *ce = dyn_cast<ConstantExpr>(a);
        ObjectPair op;
        assert(addressSpace != nullptr && "addressSpace is null!");
        uint64_t zext = ce->getZExtValue();
        // In C, you can pass any pointer to a function as long as you are careful with how you handle it.
        if (!addressSpace->resolveOne(ce, op)) {
          allocated_addr.insert(zext);
          auto addr = construct(ce, 0);
          auto zero = construct(ConstantExpr::alloc(0, Expr::Int8), 0);
          ctx.make_alloc(addr, 1, zero);
        } else {
          uint64_t addr = op.first->address;
          if(allocated_addr.count(addr) == 0) {
            std::vector<ref<Expr>> mapping = op.second->getAllBytes();
            std::vector<std::pair<int, bool>> segment_points;

            bool concrete = mapping[0]->getKind() == Expr::Constant;

            segment_points.push_back(std::make_pair(0, concrete));

            for (unsigned i = 1; i < mapping.size(); i++) {
              bool concrete1 = mapping[i]->getKind() == Expr::Constant;
              if (concrete1 != concrete) {
                segment_points.push_back(std::make_pair(i, concrete1));
                concrete = concrete1;
              }
            }

            for (unsigned i = 0; i < segment_points.size(); i++) {
              int start = segment_points[i].first;
              int end = i + 1 < segment_points.size() ? segment_points[i + 1].first : mapping.size();
              bool concrete = segment_points[i].second;

              if (concrete) {
                std::string str = "";
                for (int j = start; j < end; j++) {
                  assert(isa<ConstantExpr>(mapping[j]) && "mapping is not constantExpr!");
                  ConstantExpr* byte = dyn_cast<ConstantExpr>(mapping[j]);
                  std::stringstream ss;
                  ss << std::hex << std::setw(2) << std::setfill('0') << std::uppercase << byte->getZExtValue();
                  std::string byte_str = ss.str();
                  str += byte_str;
                }
                auto addr = construct(ConstantExpr::create(zext + start, 64), 0);
                ctx.make_alloc_seg(addr, end - start, str.c_str());
              } else {
                for (int ii = end - 1; ii >= start; ii--) {
                  KRPKNode res = construct(mapping[ii], 0);
                  auto addr = construct(ConstantExpr::create(zext + ii, 64), 0);
                  ctx.make_alloc(addr, 1, res);
                }
              }
            }
            // allocated_addr.push_back(std::make_pair(zext, mapping.size()));
            allocated_addr.insert(addr);
          }
        }
      }
      /// avoid redefinition of same ctype;
      auto it = ctype_map.find(ctype_name);
      if(it == ctype_map.end()) {
        ctype = ctx.define_ctype(ctype_name, sort);
        ctype_map.insert(std::make_pair(ctype_name, ctype));
      } else {
        ctype = it->second;
      }

      KRPKNode arg = construct(a, 0); //arg will be a concat if a is SymcreteExpr or bitvector if a is a ConstantExpr
      argstype.push_back(ctype);
      args.push_back(arg);
    }
    //unsigned resultWidth = eoee->getResult()->getWidth();
    auto returnTy = func->getReturnType();
    std::string ctype_name = "";
    KRPKNode sort, ctype;
    if(returnTy->isIntegerTy()) {
      if (returnTy->getIntegerBitWidth() == 32) {
        ctype_name = "int";
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(32)});
      } else if (returnTy->getIntegerBitWidth() == 64) {
        ctype_name = "long long";
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(64)});
      } else if (returnTy->getIntegerBitWidth() == 16) {
        ctype_name = "short";
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(16)});
      } else if (returnTy->getIntegerBitWidth() == 8) {
        ctype_name = "char";
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(8)});
      } else {
        assert(0 && "unsupported width!");
      }
    } else if(returnTy->isPointerTy()) {
        if(funcName == "memset" || funcName == "memcpy" || funcName == "mempcpy" || funcName == "memmove" || funcName == "memchr") {
          ctype_name = "void *";
        } else {
          ctype_name = "const char*";
        }
        sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(64)});
    }

    auto it = ctype_map.find(ctype_name);
      if(it == ctype_map.end()) {
        returnType = ctx.define_ctype(ctype_name, sort);
        ctype_map.insert(std::make_pair(ctype_name, returnType));
      } else {
        returnType = it->second;
      }

    //KRPKNode lhs = construct(eoe->getResult(), width_out);
    
    ///avoid redefinition of cb function.
    auto find = cb_map.find(funcName);
    KRPKNode cb;
    if(find == cb_map.end()) {
      cb = ctx.declare_cb(funcName, argstype, returnType);
      cb_map.insert(std::make_pair(funcName, cb));
    } else {
      cb = find->second;
    }

    assert(args.size() == eoe->getArgs().size() && "there some cases that extop did not handle well!");
    KRPKNode term = KRPKNode::make_apply(KRPKNode::make_qual_identifier(cb, {}), args);
    return term;
  }

  default:
    assert(0 && "unhandled Expr type");
    return KRPKNode::make_true();
  }
}

void KRPKSolverImpl::constructConstraintsFromQuery(const Query &query, std::vector<KRPKNode> &result) {
    for(auto const &constraint: query.constraints) {
        KRPKNode term = construct(constraint, 0);
        result.push_back(term);
    }
    KRPKNode term = construct(query.expr, 0);
    result.push_back(term);
}

bool KRPKSolverImpl::handleKRPKModel(const std::vector<const Array*>* objects,
    std::vector<std::vector<unsigned char>>* values, KRPKModel model) {
        if (!objects) {
            // No assignment is needed
            assert(values == NULL && "object is null while value is not null");
            return false;
        } 
        assert(values && "values cannot be nullptr");  
        values->reserve(objects->size());
        for (std::vector<const Array *>::const_iterator it = objects->begin(),
                                                    ie = objects->end();
         it != ie; ++it) {
            const Array *array = *it;
            auto lit = model.get_value_of(array);
            assert(KRPKLiteralKind::BVArray == lit.get_kind());
            assert(array->getDomain() == lit.get_bv_array_index_width_in_bits());
            assert(array->getRange() == lit.get_bv_array_value_width_in_bits());
            assert(array->size >= lit.get_bv_array_size() && "array size is less than bv size!");

            std::vector<uint8_t> index_bits(lit.get_bv_array_size());
            std::iota(index_bits.begin(), index_bits.end(), 0x00); 
            std::vector<std::vector<uint8_t>> bytes;
            for(auto index: index_bits) {
              bytes.push_back(lit.get_bv_array_value({index}));
            }
            assert(lit.get_bv_array_size() == bytes.size());
            //data stores the actual value get from fuzzer.
            std::vector<unsigned char> data;
            for(const auto &byte: bytes) {
                std::copy(byte.begin(), byte.end(), std::back_inserter(data));
            }
            values->push_back(data);
        }
        return true;
}


void KRPKSolverImpl::clearGlobalMap() {
    ctx = KRPKContext::default_();
    constant_array_map.clear();
    cb_map.clear();
    ctype_map.clear();
    allocated_addr.clear();
}

llvm::Optional<std::string> getFreshName(ref<Expr> expr) {
  auto concat = dyn_cast<ConcatExpr>(expr);
  if (concat == nullptr) {
    return llvm::None;
  }
  ReadExpr* left = dyn_cast<ReadExpr>(concat->getKid(0));
  if (left == nullptr) {
    return llvm::None;
  }
  auto arr = left->updates.root;
  if (arr == nullptr) {
    return llvm::None;
  }

  if (arr->name.rfind("colossus_fresh", 0) == 0) {
    return arr->name;
  }
  return llvm::None;
}
}