#ifndef __KRPK__
#define __KRPK__

#include <cassert>
#include <cstdint>
#include <stddef.h>
#include <stdint.h>

#define KRPK_LOGIC_ALL 0

#define KRPK_ARCH_X86 0

#define KRPK_LIT_BOOLEAN 0
#define KRPK_LIT_BITVEC 1
#define KRPK_LIT_BV_ARRAY 2

#ifdef __cplusplus
extern "C"
{
#endif

/// An AST node corresponding to different syntactic constructs in SMT-LIB 2.6.
typedef struct __KASTNode* KASTNode;

/// A fuzz solver.
typedef struct __KFuzzSolver* KFuzzSolver;

/// A solution. Can be `SAT` with a solution model or `UNKNOWN`.
typedef struct __KSolution* KSolution;

/// A solution model. Assigns each unknown constant a value.
typedef struct __KModel* KModel;

/// An array of AST nodes in a sequential layout. An auxiliary data structure.
typedef struct {
   uint64_t len;
   KASTNode* arr; 
} KASTArray;

/// A literal value. Can be a boolean (kind = 0), a bitvector (kind = 1), or a bitvector array (kind = 2).
typedef struct {
   uint8_t kind;
   union {
      struct {
          uint64_t width_in_bits;
          uint8_t* bytes;
      } bitvec;
      bool boolean;
      struct {
         uint64_t index_width_in_bits;
         uint64_t value_width_in_bits;
         uint64_t len;
         struct {
            uint8_t* index;
            uint8_t* value;
         } *index_value_pairs;
      } bv_array;
   };
} KLiteral;


/// Destruct a literal. Should be hidden behind high-level APIs.
void krpk_drop_literal(KLiteral literal);


const KASTArray krpk_make_ast_array(const KASTNode **asts, uint64_t len);


/// Make the identifier with a bald symbol `symbol` (when there's no indices) or the identifier 
/// `(_ symbol index1 index2...)` (when there are indices).
KASTNode krpk_make_identifier(const KASTNode symbol, const KASTArray indices);

/// Make a qual id with or *without* a sort qualifier. For example, `(as const (Array Int Int))` is a qual id with a sort qualifier
/// where `const` is the bald id and `(Array Int Int)` is the sort qualifier, and `bvand` is a qual id without a sort qualifier.
KASTNode krpk_make_qual_identifier(const KASTNode symbol, const KASTArray indices, const KASTNode sort);



/// Make a symbol `str`.
KASTNode krpk_make_simple_symbol(const char *str);

/// Make a quoted symbol `|str|`.
KASTNode krpk_make_quoted_symbol(const char *str);

/// Destruct an AST node. Should be hidden behind high-level APIs.
void krpk_drop_ast_node(const KASTNode ast_node);

/// Construct a fuzz solver.
KFuzzSolver krpk_make_fuzz_solver();

void krpk_fuzz_solver_set_option(KFuzzSolver fuzz_solver, const char* option, const char* value);

/// Destruct a fuzz solver. Should be hidden behind high-level APIs.
void krpk_drop_fuzz_solver(KFuzzSolver fuzz_solver);

/// Solve an SMT-LIB 2 scripts.
KSolution krpk_solver_solve(KFuzzSolver solver, KASTNode smt_script);

/// Destruct a solution. Should be hidden behind high-level APIs.
void krpk_drop_solution(KSolution solution);

/// Whether the solution is a SAT?
bool krpk_solution_is_sat(KSolution solution);

bool krpk_solution_is_unknown(KSolution solution);

/// Get the solution model when the solution is SAT.
KModel krpk_solution_get_model(KSolution solution);

/// Get the value assigned to an unknown with name `constant_name` provided by the model in a solution
/// returned by the fuzz solver.
KLiteral krpk_model_get_value(
    KModel model, 
    const char* constant_name
);

bool krpk_model_contains_value_of(
    KModel model, 
    const char* constant_name
);

KLiteral krpk_default_bv_array_literal(
   uint64_t domain,
   uint64_t range,
   uint64_t size
);

/// Make a numeral index.
KASTNode krpk_make_numeral_index(uint64_t numeral);

/// Make a symbol index where the symbol is `str`.
KASTNode krpk_make_symbol_index(const char *str);



/// Make a ground sort whose identifier is `id`.
/// A ground sort is a sort without generic parameters.
/// For example, `Int` and `(_ BitVec 32)` (`32` is an index, not a generic arg).
KASTNode krpk_make_simple_sort(const KASTNode id);

/// Make a parametric sort with generic parameters reified to `sort_args`.
/// For example,
/// ```text
/// (Array Int Int)
/// ```
/// Here, the `Int`s are the `sort_args`.
KASTNode krpk_make_parametric_sort(const KASTNode id, const KASTArray sort_args);



/// Make a spec constant that wraps a numeral (`123456`), hexadecimal (`#x7FFA`), binary (`#b010001`), string (`"SPY x FAMILY"`),
/// or decimal (`114.514`).
KASTNode krpk_make_spec_constant(const KASTNode literal);

/// Make a hexadecimal literal (wrapped in a spec constant). For example, `SpecConstant::Hexadecimal(#x7FFA)`.
KASTNode krpk_make_hex_literal(const uint8_t* bytes, const uint64_t width_in_bits);

/// Wrap a qual id into an atomic term. Atomic term is the most elementary blocks that can appear in a term.
/// Such qual ids are constructed by `krpk_make_qual_identifier`.
KASTNode krpk_make_atom(const KASTNode qual_identifier);



/// Make a set-arch command `(set-arch arch)` with 0 corresponding to X86.
KASTNode krpk_make_set_arch(const uint8_t arch);

/// Make an alloc command `(alloc addr size term)`. The width of the term should be less than the size.
/// The term must be sized, so terms with sorts like `(Array (_ BitVec 32) (_ BitVec 8))` are not allowed because they
/// do not have an exact size.
KASTNode krpk_make_alloc(const KASTNode addr, const uint64_t size, const KASTNode term);

KASTNode krpk_make_alloc_seg(const KASTNode addr, const uint64_t size, const char* hex_bytes);



/// Make an annotated AST node, e.g., `(! some_term :name some_name)`.
KASTNode krpk_make_annotated(const KASTNode func, const KASTArray args);



/// Make the term `(some_func arg1 arg2 arg3...)`
KASTNode krpk_make_apply(const KASTNode func, const KASTArray args);



/// Make the term `true`.
KASTNode krpk_make_true();

/// See [`krpk_make_true`].
KASTNode krpk_make_false();

/// Make a term `(not expr)`.
KASTNode krpk_make_not(const KASTNode expr);

/// Make a term `(=> lhs rhs)`.
KASTNode krpk_make_imply(const KASTNode lhs, const KASTNode rhs);



/// Make a term `(and arg1 arg2 arg3...)`.
KASTNode krpk_make_and(const KASTArray args);

/// See [`krpk_make_and`].
KASTNode krpk_make_or(const KASTArray args);

/// See [`krpk_make_and`].
KASTNode krpk_make_xor(const KASTArray args);

/// Make a term `(= arg1 arg2 arg3...)`.
KASTNode krpk_make_equal(const KASTArray args);

/// Make a term `(distinct arg1 arg2 arg3...)`.
KASTNode krpk_make_distinct(const KASTArray args);



/// Make a term `(bvand arg1 arg2 arg3...)`.
KASTNode krpk_make_bvand(const KASTArray exprs);

/// See [`krpk_make_bvand`].
KASTNode krpk_make_bvor(const KASTArray exprs);

/// See [`krpk_make_bvand`].
KASTNode krpk_make_bvxor(const KASTArray exprs);

/// Make a term `(bvadd arg1 arg2 arg3...)`.
KASTNode krpk_make_bvadd(const KASTArray exprs);

/// See [`krpk_make_bvadd`].
KASTNode krpk_make_bvmul(const KASTArray exprs);

/// Make a term `(concat lhs rhs)`.
KASTNode krpk_make_concat(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvnot expr)`.
KASTNode krpk_make_bvnot(const KASTNode expr);

KASTNode krpk_make_bv2bool(const KASTNode expr);
KASTNode krpk_make_bool2bv(const KASTNode expr);

/// Make a term `(bvneg expr)`.
KASTNode krpk_make_bvneg(const KASTNode expr);

/// Make a term `(bvudiv lhs rhs)`.
KASTNode krpk_make_bvudiv(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvudiv`].
KASTNode krpk_make_bvurem(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvshl lhs rhs)`.
KASTNode krpk_make_bvshl(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvlshr`].
KASTNode krpk_make_bvlshr(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvult lhs rhs)`.
KASTNode krpk_make_bvult(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvnand lhs rhs)`.
KASTNode krpk_make_bvnand(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvnand`].
KASTNode krpk_make_bvnor(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvnand`].
KASTNode krpk_make_bvxnor(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvcomp lhs rhs)`.
KASTNode krpk_make_bvcomp(const KASTNode lhs, const KASTNode rhs);

/// Make a term `(bvsub lhs rhs)`.
KASTNode krpk_make_bvsub(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvudiv`].
KASTNode krpk_make_bvsdiv(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvudiv`].
KASTNode krpk_make_bvsrem(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvudiv`].
KASTNode krpk_make_bvsmod(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvlshr`].
KASTNode krpk_make_bvashr(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvule(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvugt(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvuge(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvslt(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvsle(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvsgt(const KASTNode lhs, const KASTNode rhs);

/// See [`krpk_make_bvult`].
KASTNode krpk_make_bvsge(const KASTNode lhs, const KASTNode rhs);

KASTNode krpk_make_ite(const KASTNode cond, const KASTNode then, const KASTNode else_);

/// Make a term `((extract to from) bitvec)`.
KASTNode krpk_make_extract(uint64_t from, uint64_t to, const KASTNode bitvec);

/// Make a term `((repeat times) bitvec)`.
KASTNode krpk_make_repeat(uint64_t times, const KASTNode bitvec);

/// Make a term `((zero_extend padding) bitvec)`.
KASTNode krpk_make_zero_extend(uint64_t padding, const KASTNode bitvec);

/// See [`krpk_make_zero_extend`].
KASTNode krpk_make_sign_extend(uint64_t padding, const KASTNode bitvec);

/// Make a term `((rotate_left shift) bitvec)`.
KASTNode krpk_make_rotate_left(uint64_t shift, const KASTNode bitvec);

/// See [`krpk_make_rotate_left`].
KASTNode krpk_make_rotate_right(uint64_t shift, const KASTNode bitvec);



/// Make a term `(select array index)`.
KASTNode krpk_make_select(const KASTNode array, const KASTNode index);

/// Make a term `(ensure_index array index)`.
KASTNode krpk_make_ensure_index(const KASTNode array, const KASTNode ensured_index);

/// Make a term `(store array index value)`.
KASTNode krpk_make_store(const KASTNode array, const KASTNode index, const KASTNode value);

/// Make a term `((as const sort) value)`.
KASTNode krpk_make_array_const(const KASTNode sort, const KASTNode value);

KASTNode krpk_make_array_const_with_provided_values(const KASTNode sort, const KASTNode default_value, const char* provided_values);

/// Make a declare-const command `(declare-const const_symbol sort)` and return the constant's symbol.
KASTNode krpk_make_declare_const(const KASTNode const_symbol, const KASTNode sort);

/// Make a declare-cb command `(declare-cb func_name (param1 param2 ...) return_type)`.
KASTNode krpk_make_declare_cb(const KASTNode cb_symbol, const KASTArray param_types, const KASTNode return_type);

/// Make a declare-ctype command `(declare-ctype ctype sort)`.
KASTNode krpk_make_declare_ctype(const KASTNode ctype, const KASTNode sort);

/// Make an assertion command `(assert term)`.
KASTNode krpk_make_assertion(const KASTNode term);

/// Collect all commands into one SMT-LIB 2 script.
KASTNode krpk_make_smt_script(const KASTArray commands);

/// Clone ref-count pointers to AST nodes. Needed when the C structs are copied.
KASTNode krpk_ast_node_clone(const KASTNode node);

/// Make a set-logic command `(set-logic logic)` with 0 corresponding to ALL.
KASTNode krpk_make_set_logic(uint8_t logic);



/// Convert an AST node to debug string, stored in the buffer. The return value is the length of the string and -1 if
/// the buffer is too small.
int64_t krpk_node_debug_fmt(const KASTNode node, char* buffer, uint64_t buffer_size);


#ifdef __cplusplus
}
#endif

#endif

