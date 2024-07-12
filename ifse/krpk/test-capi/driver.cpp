#include "KRPKBuilder.h"
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

using namespace capi_test;

typedef void (*TEST_FUNC)();

void test_make_true() {
    KRPKNode true_ = KRPKNode::make_true();
    std::string str = true_.debug_fmt();
    const char* expected =
R"(Term(
    QualIdentifier(
        Simple(
            Symbol(
                Simple(
                    "true",
                ),
            ),
        ),
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_false() {
    KRPKNode true_ = KRPKNode::make_false();
    std::string str = true_.debug_fmt();
    const char* expected =
R"(Term(
    QualIdentifier(
        Simple(
            Symbol(
                Simple(
                    "false",
                ),
            ),
        ),
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_bv_literal() {
    std::vector<uint8_t> bytes = {0x01};
    KRPKNode lit = KRPKNode::make_bv_literal(bytes, 8);
    const char* expected =
        "Term(\n"
        "    SpecConstant(\n"
        "        Hexadecimal(\n"
        "            Hexadecimal {\n"
        "                digit_num: 2,\n"
        "                bytes: [\n"
        "                    1,\n"
        "                ],\n"
        "            },\n"
        "        ),\n"
        "    ),\n"
        ")";
    std::string str = lit.debug_fmt();
    assert(std::string(expected) == str);
}

void test_make_symbol() {
    KRPKNode symbol = KRPKNode::make_symbol("x");
    const char* expected = 
        "Symbol(\n"
        "    Simple(\n"
        "        \"x\",\n"
        "    ),\n"
        ")";
    std::string str = symbol.debug_fmt();
    assert(std::string(expected) == str);
}

void test_make_numeral_index() {
    KRPKNode numeral = KRPKNode::make_numeral_index(5);
    const char* expected = 
        "Index(\n"
        "    Numeral(\n"
        "        Numeral(\n"
        "            5,\n"
        "        ),\n"
        "    ),\n"
        ")";
    std::string str = numeral.debug_fmt();
    assert(std::string(expected) == str);
}

void test_make_symbol_index() {
    KRPKNode symbol = KRPKNode::make_symbol_index("y");
    const char* expected = 
        "Index(\n"
        "    Symbol(\n"
        "        Simple(\n"
        "            \"y\",\n"
        "        ),\n"
        "    ),\n"
        ")";
    std::string str = symbol.debug_fmt();
    assert(std::string(expected) == str);
} 

void test_make_simple_identifier_without_index() {
    KRPKNode symbol = KRPKNode::make_symbol("x");
    KRPKNode id = KRPKNode::make_identifier(symbol, {});
    const char* expected = 
        "Identifier(\n"
        "    Symbol(\n"
        "        Simple(\n"
        "            \"x\",\n"
        "        ),\n"
        "    ),\n"
        ")";
    std::string str = id.debug_fmt();

    assert(std::string(expected) == str);
}

void test_make_simple_identifier_with_indices() {
    KRPKNode index = KRPKNode::make_numeral_index(5);
    KRPKNode symbol = KRPKNode::make_symbol("x");
    KRPKNode id = KRPKNode::make_identifier(symbol, {index});
    const char* expected = 
        "Identifier(\n"
        "    Indexed(\n"
        "        Simple(\n"
        "            \"x\",\n"
        "        ),\n"
        "        [\n"
        "            Numeral(\n"
        "                Numeral(\n"
        "                    5,\n"
        "                ),\n"
        "            ),\n"
        "        ],\n"
        "    ),\n"
        ")";
    std::string str = id.debug_fmt();
    assert(std::string(expected) == str);
}

void test_make_apply() {
    KRPKNode arg_sym = KRPKNode::make_symbol("x");
    KRPKNode arg_id = KRPKNode::make_qual_identifier(arg_sym, {});
    KRPKNode arg_term = KRPKNode::make_atom(arg_id);
    KRPKNode func_sym = KRPKNode::make_symbol("func");
    KRPKNode func_id = KRPKNode::make_qual_identifier(func_sym, {});
    KRPKNode apply = KRPKNode::make_apply(func_id, {arg_term});
    std::string str = apply.debug_fmt();

    const char* expected = 
R"(Term(
    Apply(
        Simple(
            Symbol(
                Simple(
                    "func",
                ),
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_qualified_identifier() {
    KRPKNode symbol = KRPKNode::make_symbol("x");
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKNode id = KRPKNode::make_qual_identifier(symbol, {}, sort);
    std::string str = id.debug_fmt();
    const char* expected = 
R"(QualIdentifier(
    Qualified(
        Symbol(
            Simple(
                "x",
            ),
        ),
        Simple(
            Symbol(
                Simple(
                    "Int",
                ),
            ),
        ),
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_simple_sort() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode index = KRPKNode::make_symbol_index("a");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {index});
    std::string str = sort.debug_fmt();
    const char* expected = 
R"(Sort(
    Simple(
        Indexed(
            Simple(
                "Int",
            ),
            [
                Symbol(
                    Simple(
                        "a",
                    ),
                ),
            ],
        ),
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_parametric_sort() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Array");
    KRPKNode sort_arg_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort_arg = KRPKNode::make_simple_sort(sort_arg_sym, {});
    KRPKNode sort = KRPKNode::make_parametric_sort(sort_sym, {}, {sort_arg, sort_arg});
    std::string str = sort.debug_fmt();
    const char* expected =
R"(Sort(
    Parametric(
        Symbol(
            Simple(
                "Array",
            ),
        ),
        [
            Simple(
                Symbol(
                    Simple(
                        "Int",
                    ),
                ),
            ),
            Simple(
                Symbol(
                    Simple(
                        "Int",
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_not() {
    KRPKNode expr_sym = KRPKNode::make_symbol("x");
    KRPKNode expr_id = KRPKNode::make_qual_identifier(expr_sym, {});
    KRPKNode expr_term = KRPKNode::make_atom(expr_id);
    KRPKNode not_expr = KRPKNode::make_not(expr_term);
    std::string str = not_expr.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Simple(
            Symbol(
                Simple(
                    "not",
                ),
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

    // static KRPKNode make_imply(const KRPKNode& lhs, const KRPKNode& expr);
void test_make_imply() {
    KRPKNode lhs_sym = KRPKNode::make_symbol("x");
    KRPKNode lhs_id = KRPKNode::make_qual_identifier(lhs_sym, {});
    KRPKNode lhs_term = KRPKNode::make_atom(lhs_id);

    KRPKNode rhs_sym = KRPKNode::make_symbol("y");
    KRPKNode rhs_id = KRPKNode::make_qual_identifier(rhs_sym, {});
    KRPKNode rhs_term = KRPKNode::make_atom(rhs_id);

    KRPKNode imply_expr = KRPKNode::make_imply(lhs_term, rhs_term);
    std::string str = imply_expr.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Simple(
            Symbol(
                Simple(
                    "=>",
                ),
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "y",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_and() {
    KRPKNode expr_sym = KRPKNode::make_symbol("x");
    KRPKNode expr_id = KRPKNode::make_qual_identifier(expr_sym, {});
    KRPKNode expr_term = KRPKNode::make_atom(expr_id);
    KRPKNode not_expr = KRPKNode::make_and({expr_term, expr_term, expr_term, expr_term, expr_term});
    std::string str = not_expr.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Simple(
            Symbol(
                Simple(
                    "and",
                ),
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_extract() {
    KRPKNode expr_sym = KRPKNode::make_symbol("x");
    KRPKNode expr_id = KRPKNode::make_qual_identifier(expr_sym, {});
    KRPKNode expr_term = KRPKNode::make_atom(expr_id);
    KRPKNode extract = KRPKNode::make_extract(2, 10, expr_term);
    std::string str = extract.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Simple(
            Indexed(
                Simple(
                    "extract",
                ),
                [
                    Numeral(
                        Numeral(
                            10,
                        ),
                    ),
                    Numeral(
                        Numeral(
                            2,
                        ),
                    ),
                ],
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "x",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}
    
void test_make_store() {
    KRPKNode array_sym = KRPKNode::make_symbol("arr");
    KRPKNode array_id = KRPKNode::make_qual_identifier(array_sym, {});
    KRPKNode array_term = KRPKNode::make_atom(array_id);

    KRPKNode index_sym = KRPKNode::make_symbol("idx");
    KRPKNode index_id = KRPKNode::make_qual_identifier(index_sym, {});
    KRPKNode index_term = KRPKNode::make_atom(index_id);

    KRPKNode value_sym = KRPKNode::make_symbol("val");
    KRPKNode value_id = KRPKNode::make_qual_identifier(value_sym, {});
    KRPKNode value_term = KRPKNode::make_atom(value_id);

    KRPKNode store = KRPKNode::make_store(array_term, index_term, value_term);
    std::string str = store.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Simple(
            Symbol(
                Simple(
                    "store",
                ),
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "arr",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "idx",
                        ),
                    ),
                ),
            ),
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "val",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_make_array_const() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode domain_and_range_sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKNode array_sort_sym = KRPKNode::make_symbol("Array");
    KRPKNode array_sort = KRPKNode::make_parametric_sort(array_sort_sym, {}, {domain_and_range_sort, domain_and_range_sort});

    KRPKNode value_sym = KRPKNode::make_symbol("val");
    KRPKNode value_id = KRPKNode::make_qual_identifier(value_sym, {});
    KRPKNode value_term = KRPKNode::make_atom(value_id);

    KRPKNode array_const = KRPKNode::make_array_const(array_sort, value_term);
    std::string str = array_const.debug_fmt();
    const char* expected =
R"(Term(
    Apply(
        Qualified(
            Symbol(
                Simple(
                    "const",
                ),
            ),
            Parametric(
                Symbol(
                    Simple(
                        "Array",
                    ),
                ),
                [
                    Simple(
                        Symbol(
                            Simple(
                                "Int",
                            ),
                        ),
                    ),
                    Simple(
                        Symbol(
                            Simple(
                                "Int",
                            ),
                        ),
                    ),
                ],
            ),
        ),
        [
            QualIdentifier(
                Simple(
                    Symbol(
                        Simple(
                            "val",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == str);
}

void test_declare_constant() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKContext ctx = KRPKContext::empty();
    KRPKNode constant = ctx.declare_constant("x", sort);

    std::string constant_str = constant.debug_fmt();
    const char* constant_expected =
R"(Symbol(
    Simple(
        "x",
    ),
))";
    assert(std::string(constant_expected) == constant_str);

    std::string ctx_str = ctx.debug_fmt();
    const char* ctx_expected =
R"(SMTScript(
    SMTScript(
        [
            DeclareConst(
                Simple(
                    "x",
                ),
                Simple(
                    Symbol(
                        Simple(
                            "Int",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(ctx_expected) == ctx_str);
}

void test_define_ctype() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKContext ctx = KRPKContext::empty();
    KRPKNode ctype = ctx.define_ctype("int", sort);

    std::string ctype_str = ctype.debug_fmt();

    const char* ctype_expected =
R"(Symbol(
    Simple(
        "int",
    ),
))";
    assert(std::string(ctype_expected) == ctype_str);

    std::string ctx_str = ctx.debug_fmt();

    const char* ctx_expected =
R"(SMTScript(
    SMTScript(
        [
            DefineCType(
                Simple(
                    "int",
                ),
                Simple(
                    Symbol(
                        Simple(
                            "Int",
                        ),
                    ),
                ),
            ),
        ],
    ),
))";
    assert(std::string(ctx_expected) == ctx_str);
}

void test_declare_cb() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKContext ctx = KRPKContext::empty();
    KRPKNode ctype = ctx.define_ctype("int", sort);
    KRPKNode cb = ctx.declare_cb("abs", {ctype}, ctype);

    std::string cb_str = cb.debug_fmt();
    std::string ctx_str = ctx.debug_fmt();

    const char* cb_expected = 
R"(Symbol(
    Simple(
        "abs",
    ),
))";
    const char* ctx_expected =
R"(SMTScript(
    SMTScript(
        [
            DefineCType(
                Simple(
                    "int",
                ),
                Simple(
                    Symbol(
                        Simple(
                            "Int",
                        ),
                    ),
                ),
            ),
            DeclareCB(
                Simple(
                    "abs",
                ),
                [
                    Simple(
                        "int",
                    ),
                ],
                Simple(
                    "int",
                ),
            ),
        ],
    ),
))";
    assert(std::string(cb_expected) == cb_str);
    assert(std::string(ctx_expected) == ctx_str);
}

void test_make_assertion() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Int");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKContext ctx = KRPKContext::empty();
    KRPKNode constant = ctx.declare_constant("x", sort);
    KRPKNode expr = KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {}));
    KRPKNode term = KRPKNode::make_eq({expr, expr});
    KRPKNode assertion = ctx.make_assertion(term);

    std::string assertion_str = assertion.debug_fmt();
    std::string ctx_str = ctx.debug_fmt();

    const char* assertion_expected =
R"(Command(
    Assert(
        Apply(
            Simple(
                Symbol(
                    Simple(
                        "=",
                    ),
                ),
            ),
            [
                QualIdentifier(
                    Simple(
                        Symbol(
                            Simple(
                                "x",
                            ),
                        ),
                    ),
                ),
                QualIdentifier(
                    Simple(
                        Symbol(
                            Simple(
                                "x",
                            ),
                        ),
                    ),
                ),
            ],
        ),
    ),
))";

    const char* ctx_expected =
R"(SMTScript(
    SMTScript(
        [
            DeclareConst(
                Simple(
                    "x",
                ),
                Simple(
                    Symbol(
                        Simple(
                            "Int",
                        ),
                    ),
                ),
            ),
            Assert(
                Apply(
                    Simple(
                        Symbol(
                            Simple(
                                "=",
                            ),
                        ),
                    ),
                    [
                        QualIdentifier(
                            Simple(
                                Symbol(
                                    Simple(
                                        "x",
                                    ),
                                ),
                            ),
                        ),
                        QualIdentifier(
                            Simple(
                                Symbol(
                                    Simple(
                                        "x",
                                    ),
                                ),
                            ),
                        ),
                    ],
                ),
            ),
        ],
    ),
))";
    assert(std::string(assertion_expected) == assertion_str);
    assert(std::string(ctx_expected) == ctx_str);
}

void test_default_context() {
    KRPKContext ctx = KRPKContext::default_();
    std::string ctx_str = ctx.debug_fmt();
    const char* expected = 
R"(SMTScript(
    SMTScript(
        [
            SetLogic(
                Simple(
                    "ALL",
                ),
            ),
            SetArch(
                Simple(
                    "X86",
                ),
            ),
        ],
    ),
))";
    assert(std::string(expected) == ctx_str);
}

void test_solve_simple1() {
    KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
    KRPKNode index = KRPKNode::make_numeral_index(8);
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {index});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", sort);
    KRPKNode rhs = KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {}));

    KRPKNode lhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::BitVec == lit.get_kind());
    assert(8 == lit.get_bitvec_width_in_bits());
    auto bytes = lit.get_bitvec_bytes();
    assert(1 == bytes.size());
    assert(0x01 == bytes[0]);
}

void test_solve_simple2() {
    KRPKNode sort_sym = KRPKNode::make_symbol("Bool");
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", sort);
    KRPKNode term = KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {}));

    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::Bool == lit.get_kind());
    assert(true == lit.get_bool_value());
}

void test_solve_cb() {
    size_t int_size_in_bytes = sizeof(int);

    KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
    KRPKNode index = KRPKNode::make_numeral_index(int_size_in_bytes * 8);
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {index});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", sort);

    KRPKNode ctype = ctx.define_ctype("int", sort);
    KRPKNode cb = ctx.declare_cb("abs", {ctype}, ctype);

    KRPKNode rhs = KRPKNode::make_apply(KRPKNode::make_qual_identifier(cb, {}), {KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {}))});

    std::vector<uint8_t> lit_bytes(int_size_in_bytes, 0x00);
    lit_bytes[0] = 0x01;

    KRPKNode lhs = KRPKNode::make_bv_literal(lit_bytes, int_size_in_bytes * 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::BitVec == lit.get_kind());
    assert(8 * int_size_in_bytes == lit.get_bitvec_width_in_bits());
    auto bytes = lit.get_bitvec_bytes();
    assert(int_size_in_bytes == bytes.size());
    bool is_one = true;
    bool first = true;
    for (auto byte : bytes) {
        if ((first && 0x01 != byte) || (!first && 0x00 != byte)) {
            is_one = false;
            break;
        }
        first = false;
    }

    bool is_neg_one = true;
    for (auto byte : bytes) {
        if (0xff != byte) {
            is_neg_one = false;
            break;
        }
    }
    assert(is_one || is_neg_one);
}

void test_solve_array() {
    KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
    KRPKNode index = KRPKNode::make_numeral_index(8);
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {index});
    KRPKNode array_sym = KRPKNode::make_symbol("Array");
    KRPKNode array_sort = KRPKNode::make_parametric_sort(array_sym, {}, {sort, sort});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", array_sort);
    KRPKNode rhs = KRPKNode::make_select(
        KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})),
        KRPKNode::make_bv_literal({0x00}, 8)
    );

    KRPKNode lhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::BVArray == lit.get_kind());
    assert(1 == lit.get_bv_array_size());
    assert(8 == lit.get_bv_array_index_width_in_bits());
    assert(8 == lit.get_bv_array_value_width_in_bits());
    auto bytes = lit.get_bv_array_value({0x00});
    assert(1 == bytes.size());
    assert(0x01 == bytes[0]);
}

void test_solve_array2() {
    KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
    KRPKNode index1 = KRPKNode::make_numeral_index(8);
    KRPKNode index2 = KRPKNode::make_numeral_index(32);
    KRPKNode range_sort = KRPKNode::make_simple_sort(sort_sym, {index1});
    KRPKNode domain_sort = KRPKNode::make_simple_sort(sort_sym, {index2});
    KRPKNode array_sym = KRPKNode::make_symbol("Array");
    KRPKNode array_sort = KRPKNode::make_parametric_sort(array_sym, {}, {domain_sort, range_sort});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", array_sort);
    KRPKNode rhs1 = KRPKNode::make_select(
        KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})),
        KRPKNode::make_bv_literal({0x00, 0x00, 0x00, 0x00}, 32)
    );
    KRPKNode rhs2 = KRPKNode::make_select(
        KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {})),
        KRPKNode::make_bv_literal({0x01, 0x00, 0x00, 0x00}, 32)
    );

    KRPKNode lhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term1 = KRPKNode::make_eq({lhs, rhs1});
    KRPKNode term2 = KRPKNode::make_eq({lhs, rhs2});
    KRPKNode term = KRPKNode::make_and({term1, term2});
    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::BVArray == lit.get_kind());
    assert(2 == lit.get_bv_array_size());
    assert(32 == lit.get_bv_array_index_width_in_bits());
    assert(8 == lit.get_bv_array_value_width_in_bits());
    auto bytes_of_index0 = lit.get_bv_array_value({0x00, 0x00, 0x00, 0x00});
    assert(1 == bytes_of_index0.size());
    assert(0x01 == bytes_of_index0[0]);
    auto bytes_of_index1 = lit.get_bv_array_value({0x01, 0x00, 0x00, 0x00});
    assert(1 == bytes_of_index1.size());
    assert(0x01 == bytes_of_index1[0]);
}

void test_solve_cb_pointer() {
    KRPKNode bv_sort = KRPKNode::make_simple_sort(KRPKNode::make_symbol("BitVec"), {KRPKNode::make_numeral_index(64)});
    
    KRPKContext ctx = KRPKContext::default_();

    KRPKNode int_ctype = ctx.define_ctype("int", bv_sort);
    KRPKNode char_ptr_ctype = ctx.define_ctype("char*", bv_sort);
    KRPKNode const_char_ptr_ctype = ctx.define_ctype("const char*", bv_sort);

    KRPKNode cb = ctx.declare_cb("strchr", {const_char_ptr_ctype, int_ctype}, char_ptr_ctype);
    KRPKNode addr1 = KRPKNode::make_bv_literal({0xf0, 0x7f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 64);
    KRPKNode addr2 = KRPKNode::make_bv_literal({0xf1, 0x7f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}, 64);
    ctx.make_alloc(addr1, 1, KRPKNode::make_bv_literal({0x61}, 8));
    ctx.make_alloc(addr2, 1, KRPKNode::make_bv_literal({0x00}, 8));
    KRPKNode a = ctx.declare_constant("a", bv_sort);
    KRPKNode assertion = ctx.make_assertion(KRPKNode::make_eq({addr1, KRPKNode::make_apply(KRPKNode::make_qual_identifier(cb, {}), {addr1, KRPKNode::make_atom(KRPKNode::make_qual_identifier(a, {}))})}));
    
    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("a");

    assert(KRPKLiteralKind::BitVec == lit.get_kind());
    assert(64 == lit.get_bitvec_width_in_bits());
    auto byte = lit.get_bitvec_bytes().at(0);
    assert(0x61 == byte);
}

void test_timeout() {
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode lhs = KRPKNode::make_bv_literal({0x00}, 8);
    KRPKNode rhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();
    solver.set_timeout(2000);
    auto result = solver.solve(ctx);
    assert(result.is_unknown());
}

void test_reset_method_helper1(KRPKRawFuzzSolver &solver) {
    KRPKNode sort_sym = KRPKNode::make_symbol("BitVec");
    KRPKNode index = KRPKNode::make_numeral_index(8);
    KRPKNode sort = KRPKNode::make_simple_sort(sort_sym, {index});
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode constant = ctx.declare_constant("x", sort);
    KRPKNode rhs = KRPKNode::make_atom(KRPKNode::make_qual_identifier(constant, {}));

    KRPKNode lhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    auto result = solver.solve(ctx);
    assert(result.is_sat());

    auto model = result.get_model();
    auto lit = model.get_value_of("x");

    assert(KRPKLiteralKind::BitVec == lit.get_kind());
    assert(8 == lit.get_bitvec_width_in_bits());
    auto bytes = lit.get_bitvec_bytes();
    assert(1 == bytes.size());
    assert(0x01 == bytes[0]);
}

void test_reset_method_helper2(KRPKRawFuzzSolver &solver) {
    KRPKContext ctx = KRPKContext::default_();
    KRPKNode lhs = KRPKNode::make_bv_literal({0x00}, 8);
    KRPKNode rhs = KRPKNode::make_bv_literal({0x01}, 8);

    KRPKNode term = KRPKNode::make_eq({lhs, rhs});
    KRPKNode assertion = ctx.make_assertion(term);

    // std::string debug_info = assertion.debug_fmt();
    // std::cout << "=======================" << std::endl;
    // std::cout << debug_info << std::endl;
    // std::cout << "=======================" << std::endl;

    solver.set_timeout(2000);
    auto result = solver.solve(ctx);
    
    assert(result.is_unknown());
}

void test_reset_method() {
    KRPKRawFuzzSolver solver = KRPKRawFuzzSolver();

    test_reset_method_helper1(solver);
    test_reset_method_helper2(solver);
}

const int TEST_CASE_NUM = 31;
const TEST_FUNC TESTS[TEST_CASE_NUM] = {
    test_make_true,
    test_make_false,
    test_make_bv_literal,
    test_make_symbol,
    test_make_numeral_index,
    test_make_symbol_index,
    test_make_simple_identifier_without_index,
    test_make_simple_identifier_with_indices,
    test_make_apply,
    test_make_qualified_identifier,
    test_make_simple_sort,
    test_make_parametric_sort,
    test_make_not,
    test_make_imply,
    test_make_and,
    test_make_extract,
    test_make_store,
    test_make_array_const,
    test_declare_constant,
    test_define_ctype,
    test_declare_cb,
    test_make_assertion,
    test_default_context,
    test_solve_simple1,
    test_solve_simple2,
    test_solve_cb,
    test_solve_array,
    test_solve_array2,
    test_solve_cb_pointer,
    test_timeout,
    test_reset_method,
};

int main() {
    for (auto test : TESTS) {
        test();
    }
    return 0;
}
