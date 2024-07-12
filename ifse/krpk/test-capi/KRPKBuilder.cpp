#include "KRPKBuilder.h"
#include "krpk.h"
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace capi_test {
KRPKNode KRPKNode::make_true() {
    return KRPKNode(krpk_make_true(), {});
}

KRPKNode KRPKNode::make_false() {
    return KRPKNode(krpk_make_false(), {});
}

KRPKNode KRPKNode::make_symbol(const std::string &str) {
    return KRPKNode(krpk_make_simple_symbol(str.c_str()), {});
}

KRPKNode KRPKNode::make_identifier(const KRPKNode &symbol, const std::vector<KRPKNode>& indices) {
    const KASTNode** arr = new const KASTNode*[indices.size()];
    for (size_t i = 0; i < indices.size(); i++) {
        arr[i] = &indices[i].node;
    }
    std::vector<KRPKNode> children(indices);
    children.push_back(symbol);
    auto karr = krpk_make_ast_array(indices.size() == 0 ? nullptr : arr, indices.size());
    auto r = KRPKNode(krpk_make_identifier(symbol.node, karr), children);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_apply(const KRPKNode &func, const std::vector<KRPKNode> &args) {
    const KASTNode** arr = new const KASTNode*[args.size()];
    for (size_t i = 0; i < args.size(); i++) {
        arr[i] = &args[i].node;
    }
    std::vector<KRPKNode> children(args);
    children.push_back(func);
    KASTArray karr = krpk_make_ast_array(args.size() == 0? nullptr : arr, args.size());
    auto r = KRPKNode(krpk_make_apply(func.node, karr), children);
    delete[] arr;
    return r;
}

KRPKNode KRPKNode::make_qual_identifier(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const KRPKNode& sort) {
    const KASTNode** arr = new const KASTNode*[indices.size()];
    for (size_t i = 0; i < indices.size(); i++) {
        arr[i] = &indices[i].node;
    }
    std::vector<KRPKNode> children(indices);
    children.push_back(sort);
    children.push_back(symbol);
    auto karr = krpk_make_ast_array(indices.size() == 0 ? nullptr : arr, indices.size());
    auto r = KRPKNode(krpk_make_qual_identifier(symbol.node, karr, sort.node), children);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_atom(const KRPKNode& qual_id) {
    return KRPKNode(krpk_make_atom(qual_id.node), {qual_id});
}

KRPKNode KRPKNode::make_numeral_index(const int numeral) {
    return KRPKNode(krpk_make_numeral_index(numeral), {});
}

KRPKNode KRPKNode::make_symbol_index(const std::string& str) {
    return KRPKNode(krpk_make_symbol_index(str.c_str()), {});
}

KRPKNode KRPKNode::make_simple_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices) {
    auto id = make_identifier(symbol, indices);
    auto r = KRPKNode(krpk_make_simple_sort(id.node), {id});
    return r;
}

KRPKNode KRPKNode::make_bv_literal(const std::vector<uint8_t>& bytes, size_t width_in_bits) {
    auto spec_const = KRPKNode(krpk_make_hex_literal(bytes.data(), width_in_bits), {});
    return KRPKNode(krpk_make_spec_constant(spec_const.node), {spec_const});
}

KRPKNode KRPKNode::make_parametric_sort(const KRPKNode& symbol, const std::vector<KRPKNode>& indices, const std::vector<KRPKNode>& sort_args) {
    const KASTNode** arr = new const KASTNode*[sort_args.size()];
    for (size_t i = 0; i < sort_args.size(); i++) {
        arr[i] = &sort_args[i].node;
    }
    std::vector<KRPKNode> children = sort_args;
    auto id = make_identifier(symbol, indices);
    children.push_back(id);
    auto karr = krpk_make_ast_array(sort_args.size() == 0 ? nullptr : arr, sort_args.size());
    auto r = KRPKNode(krpk_make_parametric_sort(id.node, karr), children);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_or(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_or(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_xor(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_xor(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_eq(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_equal(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_distinct(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_distinct(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_not(const KRPKNode& expr) {
    return KRPKNode(krpk_make_not(expr.node), {});
}

KRPKNode KRPKNode::make_imply(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_imply(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_and(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_and(karr), exprs);
    delete [] arr;
    return r;
}
    

KRPKNode KRPKNode::make_concat(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_concat(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvnot(const KRPKNode& expr) {
    return KRPKNode(krpk_make_bvnot(expr.node), {expr});
}

KRPKNode KRPKNode::make_bv2bool(const KRPKNode& expr) {
    return KRPKNode(krpk_make_bv2bool(expr.node), {expr});
}

KRPKNode KRPKNode::make_bool2bv(const KRPKNode& expr) {
    return KRPKNode(krpk_make_bool2bv(expr.node), {expr});
}

KRPKNode KRPKNode::make_bvand(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_bvand(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_bvor(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_bvor(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_bvxor(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_bvxor(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_bvneg(const KRPKNode& expr) {
    return KRPKNode(krpk_make_bvneg(expr.node), {expr});
}

KRPKNode KRPKNode::make_bvadd(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_bvadd(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_bvmul(const std::vector<KRPKNode>& exprs) {
    const KASTNode** arr = new const KASTNode*[exprs.size()];
    for (size_t i = 0; i < exprs.size(); i++) {
        arr[i] = &exprs[i].node;
    }
    auto karr = krpk_make_ast_array(exprs.size() == 0 ? nullptr : arr, exprs.size());
    auto r = KRPKNode(krpk_make_bvmul(karr), exprs);
    delete [] arr;
    return r;
}

KRPKNode KRPKNode::make_bvudiv(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvudiv(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvurem(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvurem(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvshl(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvshl(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvlshr(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvlshr(lhs.node, rhs.node), {lhs, rhs});
}
    
KRPKNode KRPKNode::make_bvult(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvult(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvnand(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvnand(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvnor(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvnor(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvxnor(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvxnor(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvcomp(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvcomp(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsub(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsub(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsdiv(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsdiv(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsrem(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsrem(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvuge(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvuge(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvslt(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvslt(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsle(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsle(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsgt(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsgt(lhs.node, rhs.node), {lhs, rhs});
}

KRPKNode KRPKNode::make_bvsge(const KRPKNode& lhs, const KRPKNode& rhs) {
    return KRPKNode(krpk_make_bvsge(lhs.node, rhs.node), {lhs, rhs});
}
KRPKNode KRPKNode::make_extract(const int from, const int to, const KRPKNode& bitvec) {
    return KRPKNode(krpk_make_extract(from, to, bitvec.node), {bitvec});
}
KRPKNode KRPKNode::make_zero_extend(const uint64_t padding, const KRPKNode& bitvec) {
    return KRPKNode(krpk_make_zero_extend(padding, bitvec.node), {bitvec});
}
KRPKNode KRPKNode::make_sign_extend(const uint64_t padding, const KRPKNode& bitvec){
    return KRPKNode(krpk_make_sign_extend(padding, bitvec.node), {bitvec});
}
KRPKNode KRPKNode::make_rotate_left(const uint64_t shift, const KRPKNode& bitvec) {
    return KRPKNode(krpk_make_rotate_left(shift, bitvec.node), {bitvec});
}
KRPKNode KRPKNode::make_rotate_right(const uint64_t shift, const KRPKNode& bitvec) {
    return KRPKNode(krpk_make_rotate_right(shift, bitvec.node), {bitvec});
}

KRPKNode KRPKNode::make_select(const KRPKNode& array, const KRPKNode& index) {
    return KRPKNode(krpk_make_select(array.node, index.node), {array, index});
}
KRPKNode KRPKNode::make_store(const KRPKNode& array, const KRPKNode& index, const KRPKNode& value) {
    return KRPKNode(krpk_make_store(array.node, index.node, value.node), {array, index, value});
}
KRPKNode KRPKNode::make_array_const(const KRPKNode& sort, const KRPKNode& value) {
    return KRPKNode(krpk_make_array_const(sort.node, value.node), {sort, value});
}

KRPKNode KRPKContext::declare_constant(const std::string& constant_name, const KRPKNode& sort) {
    auto symbol = KRPKNode::make_symbol(constant_name);
    auto const_delare = KRPKNode(krpk_make_declare_const(symbol.node, sort.node), {symbol, sort});
    declared_cbs.emplace(symbol, const_delare);
    return symbol;
}

KRPKNode KRPKContext::define_ctype(const std::string& ctype_name, const KRPKNode& sort) {
    auto symbol = KRPKNode::make_symbol(ctype_name);
    auto ctype_declare = KRPKNode(krpk_make_declare_ctype(symbol.node, sort.node), {symbol, sort});
    declared_ctypes.emplace(symbol, ctype_declare);
    return symbol;
}

KRPKNode KRPKContext::declare_cb(const std::string& cb_function_name, const std::vector<KRPKNode>& param_types, const KRPKNode& return_type) {
    auto symbol = KRPKNode::make_symbol(cb_function_name);
    const KASTNode** arr = new const KASTNode*[param_types.size()];
    for (size_t i = 0; i < param_types.size(); i++) {
        arr[i] = &param_types[i].node;
    }
    auto karr = krpk_make_ast_array(param_types.size() == 0 ? nullptr : arr, param_types.size());
    auto cb_declare = krpk_make_declare_cb(symbol.node, karr, return_type.node);
    std::vector<KRPKNode> children = param_types;
    children.push_back(symbol);
    children.push_back(return_type);
    auto r = KRPKNode(cb_declare, children);
    declared_cbs.emplace(symbol, r);
    delete [] arr;
    return symbol;
}

KRPKNode KRPKContext::make_assertion(const KRPKNode& term) {
    auto r = KRPKNode(krpk_make_assertion(term.node), {term});
    assertions.push_back(r);
    return r;
}

KRPKNode KRPKContext::smt_script() const {
    auto command_num = (arch_uninitialized() ? 0 : 1) + (logic_uninitialized() ? 0 : 1) + declared_ctypes.size() + declared_constants.size() + declared_cbs.size() + allocs.size() + assertions.size();
    const KASTNode** commands = new const KASTNode*[command_num];
    std::vector<KRPKNode> children(command_num);
    size_t i = 0;

    if (!logic_uninitialized()) {
        commands[i++] = &set_logic_command.node;
        children.push_back(set_logic_command);
    }

    if (!arch_uninitialized()) {
        commands[i++] = &set_arch_command.node;
        children.push_back(set_arch_command);
    }

    for (auto& p : declared_ctypes) {
        commands[i++] = &p.second.node;
        children.push_back(p.second);
    }
    for (auto& p : declared_constants) {
        commands[i++] = &p.second.node;
        children.push_back(p.second);
    }
    for (auto& p : declared_cbs) {
        commands[i++] = &p.second.node;
        children.push_back(p.second);
    }
    for (auto& p : allocs) {
        commands[i++] = &p.node;
        children.push_back(p);
    }
    for (auto& p : assertions) {
        commands[i++] = &p.node;
        children.push_back(p);
    }
    auto karr = krpk_make_ast_array(i == 0 ? nullptr : commands, i);
    auto script = krpk_make_smt_script(karr);
    delete [] commands;
    
    auto r = KRPKNode(script, children);
    return r;
}

uint64_t bytes_to_u64(const uint8_t* bytes, size_t len) {
    uint64_t r = 0;
    for (size_t i = 0; i < len; i++) {
        r |= ((uint64_t)bytes[i]) << (i * 8);
    }
    return r;
}

std::unordered_map<uint64_t, std::vector<uint8_t>>& KRPKLiteral::get_bv_array() const {
    assert(this->get_kind() == KRPKLiteralKind::BVArray);
    assert(this->get_bv_array_index_width_in_bits() == 8 || this->get_bv_array_index_width_in_bits() == 16 || this->get_bv_array_index_width_in_bits() == 32 || this->get_bv_array_index_width_in_bits() == 64);
    if (this->bv_array_cache.empty()) {
        for (size_t i = 0; i < literal.bv_array.len; i++) {
            uint8_t* index_ptr = literal.bv_array.index_value_pairs[i].index;
            uint64_t index_value = bytes_to_u64(index_ptr, this->get_bv_array_index_width_in_bits() / 8);
            
            size_t value_width_in_bytes = this->get_bv_array_value_width_in_bits() / 8 + (this->get_bv_array_value_width_in_bits() % 8 == 0 ? 0 : 1);
            std::vector<uint8_t> value_value(value_width_in_bytes);
            for (size_t j = 0; j < value_width_in_bytes; j++) {
                value_value[j] = literal.bv_array.index_value_pairs[i].value[j];
            }

            this->bv_array_cache[index_value] = value_value;
        }
    }
    return this->bv_array_cache;
}

std::vector<uint8_t>& KRPKLiteral::get_bv_array_value(const std::vector<uint8_t>& index) const {
    auto& bv_array = this->get_bv_array();
    uint64_t index_value = bytes_to_u64(index.data(), index.size());
    return bv_array.at(index_value);
}

size_t KRPKLiteral::get_bv_array_index_width_in_bits() const {
    return this->literal.bv_array.index_width_in_bits;
}

size_t KRPKLiteral::get_bv_array_value_width_in_bits() const {
    return this->literal.bv_array.value_width_in_bits;
}

void KRPKContext::make_alloc(const KRPKNode& addr, const uint64_t size, const KRPKNode& term) {
    auto r = KRPKNode(krpk_make_alloc(addr.node, size, term.node), {addr, term});
    allocs.push_back(r);
}
}