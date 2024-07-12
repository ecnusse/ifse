#ifndef KLEE_KRPKBUILDER_H
#define KLEE_KRPKBUILDER_H

#include "klee/Expr/Expr.h"
#include "klee/Support/ErrorHandling.h"
#include "krpk.h"
#include "llvm/Support/raw_ostream.h"
#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>
#include <cstdint>
#include <cassert>

namespace klee {
class KRPKNode {
friend class KRPKRawFuzzSolver;
friend class KRPKContext;
friend struct std::hash<klee::KRPKNode>;
private:
    // int* refCount;
    KASTNode node;
    std::vector<KRPKNode> children; // Record children to avoid memory leak.

    KRPKNode(KASTNode node, const std::vector<KRPKNode>& children) : node(node), children(children) {}
public:

    std::vector<KRPKNode> getChildren() const {return children;}

    KRPKNode() : node(nullptr) {}

    static KRPKNode null() {
        return KRPKNode();
    }

    bool is_null() const {
        return node == nullptr;
    }

    static KRPKNode make_true();
    static KRPKNode make_false();
    static KRPKNode make_symbol(const std::string& str);
    static KRPKNode make_identifier(const KRPKNode& symbol, const std::vector<KRPKNode>& indices);
    static KRPKNode make_apply(const KRPKNode& func, const std::vector<KRPKNode>& args);
    static KRPKNode make_qual_identifier(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const KRPKNode& sort = KRPKNode::null());
    static KRPKNode make_atom(const KRPKNode& qual_id);
    static KRPKNode make_numeral_index(const int numeral);
    static KRPKNode make_symbol_index(const std::string& str);
    static KRPKNode make_parametric_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const std::vector<KRPKNode>& sort_args);
    static KRPKNode make_simple_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices);
    static KRPKNode make_bv_literal(const std::vector<uint8_t>& bytes, size_t width_in_bits);
    static KRPKNode make_not(const KRPKNode& expr);
    static KRPKNode make_imply(const KRPKNode& lhs, const KRPKNode& expr);
    static KRPKNode make_and(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_or(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_xor(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_eq(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_distinct(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bv2bool(const KRPKNode& expr);
    static KRPKNode make_bool2bv(const KRPKNode& expr);
    static KRPKNode make_concat(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvnot(const KRPKNode& expr);
    static KRPKNode make_bvand(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bvor(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bvneg(const KRPKNode& expr);
    static KRPKNode make_bvadd(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bvmul(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bvudiv(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvurem(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvshl(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvlshr(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvult(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvnand(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvnor(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvxor(const std::vector<KRPKNode>& exprs);
    static KRPKNode make_bvxnor(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvcomp(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsub(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsdiv(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsrem(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsmod(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvashr(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvule(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvugt(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvuge(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvslt(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsle(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsgt(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_bvsge(const KRPKNode& lhs, const KRPKNode& rhs);
    static KRPKNode make_ite(const KRPKNode& cond, const KRPKNode& then, const KRPKNode& els);

    static KRPKNode make_extract(const int from, const int to, const KRPKNode& bitvec);
    static KRPKNode make_zero_extend(const uint64_t padding, const KRPKNode& bitvec);
    static KRPKNode make_sign_extend(const uint64_t padding, const KRPKNode& bitvec);
    static KRPKNode make_rotate_left(const uint64_t shift, const KRPKNode& bitvec);
    static KRPKNode make_rotate_right(const uint64_t shift, const KRPKNode& bitvec);

    static KRPKNode make_select(const KRPKNode& array, const KRPKNode& index);
    static KRPKNode make_ensure_index(const KRPKNode& array, const KRPKNode& index);
    static KRPKNode make_store(const KRPKNode& array, const KRPKNode& index, const KRPKNode& value);
    static KRPKNode make_array_const(const KRPKNode& sort, const KRPKNode& value);
    static KRPKNode make_array_const_with_provided_values(const KRPKNode& sort, const KRPKNode& default_value, const char* provided_values);
    
    KRPKNode(const KRPKNode& other) : node(other.node == nullptr ? nullptr : krpk_ast_node_clone(other.node)), children(other.children) {}
    
    KRPKNode clone() {
        return KRPKNode(*this);
    }
    
    KRPKNode& operator=(const KRPKNode& other) {
        if (node != nullptr) {
            krpk_drop_ast_node(node);
        }
        node = other.node == nullptr ? nullptr : krpk_ast_node_clone(other.node);
        children.clear();
        for (const KRPKNode& child : other.children) {
            children.push_back(child);
        }
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

    std::string debug_fmt() {
        const size_t BUFFER_SIZE = 1024000;
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
    KRPKLogic_ALL,
};

enum KRPKArch {
    X86,
};

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
        for (unsigned i = 0; i < width_in_bytes; i++) {
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
struct std::hash<klee::KRPKNode> {
    size_t operator()(const klee::KRPKNode& k) const {
        return std::hash<KASTNode>()(k.node);
    }
};


namespace klee{
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

    
public:

    KRPKContext() : set_logic_command(KRPKNode::null()), set_arch_command(KRPKNode::null()){}
    
    static KRPKContext empty() {
        return KRPKContext();
    }
    
    static KRPKContext default_() {
        KRPKContext context = KRPKContext::empty();

        context.set_arch(KRPKArch::X86);
        context.set_logic(KRPKLogic::KRPKLogic_ALL);
        return context;
    }

    KRPKNode declare_constant(const std::string& constant_name, const KRPKNode& sort);
    KRPKNode define_ctype(const std::string& ctype_name, const KRPKNode& sort);
    KRPKNode declare_cb(const std::string& cb_function_name, const std::vector<KRPKNode>& param_types, const KRPKNode& return_type);
    KRPKNode make_assertion(const KRPKNode& term);
    void make_alloc(const KRPKNode& addr, const uint64_t size, const KRPKNode& term);
    void make_alloc_seg(const KRPKNode& addr, const uint64_t size, const char* hex_bytes);

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
        case KRPKLogic::KRPKLogic_ALL:
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

class KRPKModel {
private:
    KModel model;
public:
    KRPKModel(KModel model) : model(model) {}
    ~KRPKModel() {}
    KRPKLiteral get_value_of(const std::string& constant_name) {
        return KRPKLiteral(krpk_model_get_value(model, constant_name.c_str()));
    }

    KRPKLiteral get_value_of(const Array* constant) {
        bool contains = krpk_model_contains_value_of(model, constant->name.c_str());
        
        if (!contains) {
            auto domain = constant->domain;
            auto range = constant->range;
            auto size = constant->size;
            return KRPKLiteral(krpk_default_bv_array_literal(domain, range, size));
        }

        return KRPKLiteral(krpk_model_get_value(model, constant->name.c_str()));
    }
};

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
