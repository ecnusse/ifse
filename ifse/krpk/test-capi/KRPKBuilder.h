#ifndef CAPI_TEST_KRPKBUILDER_H
#define CAPI_TEST_KRPKBUILDER_H

#include "krpk.h"
#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>
#include <cstdint>
#include <cassert>

namespace capi_test {

/// An AST node corresponding to different syntactic constructs in SMT-LIB 2.6.
/// This is a wrapper around the C API. The memory will be automatically released when the object is destructed.
class KRPKNode {
friend class KRPKRawFuzzSolver;
friend class KRPKContext;
friend struct std::hash<capi_test::KRPKNode>;
private:
    KASTNode node;
    const std::vector<KRPKNode> children; // Record children to avoid memory leak.

    KRPKNode(KASTNode node, const std::vector<KRPKNode>& children) : node(node), children(children) {}
public:
    KRPKNode() : node(nullptr) {}

    static KRPKNode null() {
        return KRPKNode();
    }

    bool is_null() const {
        return node == nullptr;
    }

    /// Make the term `true`.
    static KRPKNode make_true();

    /// See [`make_true`].
    static KRPKNode make_false();

    static KRPKNode make_symbol(const std::string& str);

    /// Make the identifier with a bald symbol `symbol` (when there's no indices) or the identifier 
    /// `(_ symbol index1 index2...)` (when there are indices).
    static KRPKNode make_identifier(const KRPKNode& symbol, const std::vector<KRPKNode>& indices);

    /// Make the term `(some_func arg1 arg2 arg3...)`
    static KRPKNode make_apply(const KRPKNode& func, const std::vector<KRPKNode>& args);

    /// Make a qual id with or *without* a sort qualifier. For example, `(as const (Array Int Int))` is a qual id with a sort qualifier
    /// where `const` is the bald id and `(Array Int Int)` is the sort qualifier, and `bvand` is a qual id without a sort qualifier.
    static KRPKNode make_qual_identifier(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const KRPKNode& sort = KRPKNode::null());

    /// Wrap a qual id into an atomic term. Atomic term is the most elementary blocks that can appear in a term.
    /// Such qual ids are constructed by `make_qual_identifier`.
    static KRPKNode make_atom(const KRPKNode& qual_id);

    /// Make a numeral index.
    static KRPKNode make_numeral_index(const int numeral);

    /// Make a symbol index where the symbol is `str`.
    static KRPKNode make_symbol_index(const std::string& str);

    /// Make a parametric sort with generic parameters reified to `sort_args`.
    /// For example,
    /// ```text
    /// (Array Int Int)
    /// ```
    /// Here, the `Int`s are the `sort_args`.
    static KRPKNode make_parametric_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const std::vector<KRPKNode>& sort_args);

    /// Make a ground sort whose identifier is `id`.
    /// A ground sort is a sort without generic parameters.
    /// For example, `Int` and `(_ BitVec 32)` (`32` is an index, not a generic arg).
    static KRPKNode make_simple_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices);

    static KRPKNode make_bv_literal(const std::vector<uint8_t>& bytes, size_t width_in_bits);

    /// Make a term `(not expr)`.
    static KRPKNode make_not(const KRPKNode& expr);

    /// Make a term `(=> lhs rhs)`.
    static KRPKNode make_imply(const KRPKNode& lhs, const KRPKNode& expr);

    /// Make a term `(and arg1 arg2 arg3...)`.
    static KRPKNode make_and(const std::vector<KRPKNode>& exprs);

    /// See [`make_and`].
    static KRPKNode make_or(const std::vector<KRPKNode>& exprs);

    /// See [`make_and`].
    static KRPKNode make_xor(const std::vector<KRPKNode>& exprs);

    static KRPKNode make_eq(const std::vector<KRPKNode>& exprs);

    /// Make a term `(distinct arg1 arg2 arg3...)`.
    static KRPKNode make_distinct(const std::vector<KRPKNode>& exprs);

    /// Make a term `(concat lhs rhs)`.
    static KRPKNode make_concat(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvnot expr)`.
    static KRPKNode make_bvnot(const KRPKNode& expr);
    
    static KRPKNode make_bv2bool(const KRPKNode& expr);
    static KRPKNode make_bool2bv(const KRPKNode& expr);

    /// Make a term `(bvand arg1 arg2 arg3...)`.
    static KRPKNode make_bvand(const std::vector<KRPKNode>& exprs);

    /// See [`make_bvand`].
    static KRPKNode make_bvor(const std::vector<KRPKNode>& exprs);

    /// Make a term `(bvneg expr)`.
    static KRPKNode make_bvneg(const KRPKNode& expr);

    /// Make a term `(bvadd arg1 arg2 arg3...)`.
    static KRPKNode make_bvadd(const std::vector<KRPKNode>& exprs);

    /// See [`make_bvadd`].
    static KRPKNode make_bvmul(const std::vector<KRPKNode>& exprs);

    /// Make a term `(bvudiv lhs rhs)`.
    static KRPKNode make_bvudiv(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvudiv`].
    static KRPKNode make_bvurem(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvshl lhs rhs)`.
    static KRPKNode make_bvshl(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvlshr`].
    static KRPKNode make_bvlshr(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvult lhs rhs)`.
    static KRPKNode make_bvult(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvnand lhs rhs)`.
    static KRPKNode make_bvnand(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvnand`].
    static KRPKNode make_bvnor(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvand`].
    static KRPKNode make_bvxor(const std::vector<KRPKNode>& exprs);

    /// See [`make_bvnand`].
    static KRPKNode make_bvxnor(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvcomp lhs rhs)`.
    static KRPKNode make_bvcomp(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `(bvsub lhs rhs)`.
    static KRPKNode make_bvsub(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvudiv`].
    static KRPKNode make_bvsdiv(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvudiv`].
    static KRPKNode make_bvsrem(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvudiv`].
    static KRPKNode make_bvsmod(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvlshr`].
    static KRPKNode make_bvashr(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvule(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvugt(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvuge(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvslt(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvsle(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvsgt(const KRPKNode& lhs, const KRPKNode& rhs);

    /// See [`make_bvult`].
    static KRPKNode make_bvsge(const KRPKNode& lhs, const KRPKNode& rhs);

    /// Make a term `((extract to from) bitvec)`.
    static KRPKNode make_extract(const int from, const int to, const KRPKNode& bitvec);

    /// Make a term `((zero_extend padding) bitvec)`.
    static KRPKNode make_zero_extend(const uint64_t padding, const KRPKNode& bitvec);

    /// See [`make_zero_extend`].
    static KRPKNode make_sign_extend(const uint64_t padding, const KRPKNode& bitvec);

    /// Make a term `((rotate_left shift) bitvec)`.
    static KRPKNode make_rotate_left(const uint64_t shift, const KRPKNode& bitvec);

    /// See [`make_rotate_left`].
    static KRPKNode make_rotate_right(const uint64_t shift, const KRPKNode& bitvec);



    /// Make a term `(select array index)`.
    static KRPKNode make_select(const KRPKNode& array, const KRPKNode& index);

    /// Make a term `(store array index value)`.
    static KRPKNode make_store(const KRPKNode& array, const KRPKNode& index, const KRPKNode& value);

    /// Make a term `((as const sort) value)`.
    static KRPKNode make_array_const(const KRPKNode& sort, const KRPKNode& value);

    
    KRPKNode(const KRPKNode& other) : node(other.node == nullptr ? nullptr : krpk_ast_node_clone(other.node)) {}

    KRPKNode& operator=(const KRPKNode& other) {
        if (node != nullptr) {
            krpk_drop_ast_node(node);
        }
        node = other.node == nullptr ? nullptr : krpk_ast_node_clone(other.node);
        return *this;
    }
    
    ~KRPKNode() {
        if (node == nullptr) {
            return;
        }
        krpk_drop_ast_node(node);
    }

    bool operator==(const KRPKNode& other) const {
        return node == other.node;
    }

    /// Format the node into a string.
    std::string debug_fmt() {
        const size_t BUFFER_SIZE = 10240;
        char buffer[BUFFER_SIZE];
        int len = krpk_node_debug_fmt(node, buffer, BUFFER_SIZE);
        if (len != -1) {
            return std::string(buffer, len);
        } else {
            return std::string(buffer, BUFFER_SIZE);
        }
    }
};

enum KRPKLiteralKind {
    BitVec,
    Bool,
    BVArray,
};

enum KRPKLogic {
    ALL,
};

enum KRPKArch {
    X86,
};

/// A literal value assigned to an unknown constant in the solution model when a SMT query is successfully solved.
class KRPKLiteral {
friend class KRPKModel;
private:
    KLiteral literal;
    KRPKLiteral(KLiteral literal) : literal(literal) {}

    mutable std::unordered_map<uint64_t, std::vector<uint8_t>> bv_array_cache;

    std::unordered_map<uint64_t, std::vector<uint8_t>>& get_bv_array() const;
public:
    ~KRPKLiteral() {
        krpk_drop_literal(literal);
    }
    KRPKLiteralKind get_kind() const {
        switch (literal.kind) {
        case KRPK_LIT_BOOLEAN:
            return KRPKLiteralKind::Bool;
        case KRPK_LIT_BITVEC:
            return KRPKLiteralKind::BitVec;
        case KRPK_LIT_BV_ARRAY:
            return KRPKLiteralKind::BVArray;
        default:
            assert(false);
        }
    }

    std::vector<uint8_t> get_bitvec_bytes() {
        std::vector<uint8_t> bytes;
        size_t width_in_bytes = literal.bitvec.width_in_bits / 8 + (literal.bitvec.width_in_bits % 8 == 0 ? 0 : 1);
        for (int i = 0; i < width_in_bytes; i++) {
            bytes.push_back(literal.bitvec.bytes[i]);
        }
        return bytes;
    }

    std::vector<uint8_t>& get_bv_array_value(const std::vector<uint8_t>& index) const;

    size_t get_bv_array_index_width_in_bits() const;

    size_t get_bv_array_value_width_in_bits() const;

    size_t get_bitvec_width_in_bits() {
        return literal.bitvec.width_in_bits;
    }
    bool get_bool_value() {
        return literal.boolean;
    }

    size_t get_bv_array_size() const {
        return literal.bv_array.len;
    }
};
}


template<>
struct std::hash<capi_test::KRPKNode> {
    size_t operator()(const capi_test::KRPKNode& k) const {
        return std::hash<KASTNode>()(k.node);
    }
};


namespace capi_test {

/// A context stored all assertions, memory allocations, and declarations of unknown constants, C types and close-box functions.
class KRPKContext {
friend class KRPKRawFuzzSolver;
private:
    std::unordered_map<KRPKNode, KRPKNode> declared_constants;
    std::unordered_map<KRPKNode, KRPKNode> declared_ctypes;
    std::unordered_map<KRPKNode, KRPKNode> declared_cbs;

    std::vector<KRPKNode> assertions;
    std::vector<KRPKNode> allocs;

    KRPKNode smt_script() const;

    KRPKLogic logic;
    KRPKNode set_logic_command;

    KRPKArch arch;
    KRPKNode set_arch_command;

    KRPKContext() : set_logic_command(KRPKNode::null()), set_arch_command(KRPKNode::null()){}
public:
    /// Empty context with the logic and the arch undefined.
    static KRPKContext empty() {
        return KRPKContext();
    }

    /// Default context with the logic being ALL and the arch being X86.
    static KRPKContext default_() {
        KRPKContext context = KRPKContext::empty();
        context.set_logic(KRPKLogic::ALL);
        context.set_arch(KRPKArch::X86);
        return context;
    }

    KRPKNode declare_constant(const std::string& constant_name, const KRPKNode& sort);

    KRPKNode define_ctype(const std::string& ctype_name, const KRPKNode& sort);

    KRPKNode declare_cb(const std::string& cb_function_name, const std::vector<KRPKNode>& param_types, const KRPKNode& return_type);

    KRPKNode make_assertion(const KRPKNode& term);

    /// Alloc a memory address with some size and assign the bytes to a term. The term must be exactly sized (so cannot be an array) and
    /// its width must be less or equal than the size. Also, the allocation cannot overlap another allocation.
    /// Before make an allocation, you must set the architecture by (set-arch ARCH) to designate the address width.
    /// For example, if you `(set-arch X86)`, the address must be a 64-bit hexadecimal.
    void make_alloc(const KRPKNode& addr, const uint64_t size, const KRPKNode& term);

    KRPKLogic get_logic() const {
        return logic;
    }

    KRPKArch get_arch() const {
        return arch;
    }

    KRPKLogic set_logic(KRPKLogic logic_) {
        KRPKLogic previous = get_logic();
        this->logic = logic_;

        uint8_t raw_logic_value;
        switch (logic_) {
        case KRPKLogic::ALL:
            raw_logic_value = KRPK_LOGIC_ALL;
            break;
        default:
            assert(false); // unimplemented
        }

        KRPKNode set_logic_command = KRPKNode(krpk_make_set_logic(raw_logic_value), {});
        this->set_logic_command = set_logic_command;

        return previous;
    }

    KRPKArch set_arch(KRPKArch arch_) {
        KRPKArch previous = get_arch();
        this->arch = arch_;

        uint8_t raw_arch_value;
        switch (arch_) {
        case KRPKArch::X86:
            raw_arch_value = KRPK_ARCH_X86;
            break;
        default:
            assert(false); // unimplemented
        }

        KRPKNode set_arch_command = KRPKNode(krpk_make_set_arch(raw_arch_value), {});
        this->set_arch_command = set_arch_command;

        return previous;
    }

    std::string debug_fmt() {
        return smt_script().debug_fmt();
    }

    bool logic_uninitialized() const {
        return set_logic_command.is_null();
    }

    bool arch_uninitialized() const {
        return set_arch_command.is_null();
    }
};

/// A solution model when the SMT query is successfully solved.
class KRPKModel {
private:
    KModel model;
public:
    KRPKModel(KModel model) : model(model) {}
    ~KRPKModel() {}
    KRPKLiteral get_value_of(const std::string& constant_name) {
        return KRPKLiteral(krpk_model_get_value(model, constant_name.c_str()));
    }
};

/// Solution to an SMT query, can be `SAT` (with a solution model) and `UNKNOWN`.
class KRPKSolution {
private:
    KSolution solution;
public:
    KRPKSolution(KSolution solution) : solution(solution) {}
    ~KRPKSolution() {
        krpk_drop_solution(solution);
    }
    bool is_sat() {
        return krpk_solution_is_sat(solution);
    }
    bool is_unknown() {
        return krpk_solution_is_unknown(solution);
    }
    KRPKModel get_model() {
        return KRPKModel(krpk_solution_get_model(solution));
    }
};

/// A fuzz solver.
class KRPKRawFuzzSolver {
private:
    KFuzzSolver solver;
    KRPKSolution solve(const KRPKNode& smt_script) {
        return KRPKSolution(krpk_solver_solve(solver, smt_script.node));
    }
public:
    KRPKRawFuzzSolver() : solver(krpk_make_fuzz_solver()) {}
    ~KRPKRawFuzzSolver() {
        krpk_drop_fuzz_solver(solver);
    }
    KRPKSolution solve(const KRPKContext& context) {
        return solve(context.smt_script());
    }

    void set_timeout(const uint64_t timeout_in_milliseconds) {
        krpk_fuzz_solver_set_option(solver, "max_time_in_milliseconds", std::to_string(timeout_in_milliseconds).c_str());
    }
};

}


#endif

