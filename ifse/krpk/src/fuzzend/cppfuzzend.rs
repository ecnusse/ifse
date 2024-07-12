use std::collections::HashMap;
use std::rc::Rc;

use either::Either;

use crate::mir::{
    DeclaredConstant, FuzzProgram, IRKind, IRRef, LiteralValue, MemoryProxy, Type, ValueRef,
};
use crate::smtanalyze::KRPKCBFunctionDecl;

use super::{FuzzEnd, Fuzzer, LibFuzzer};
use itertools::Itertools;
use trim_margin::MarginTrimmable;

/// A fuzz end that transforms a fuzz program to a C++ program. Suitable for fuzzers using C++.
pub struct CPPFuzzEnd {
    fuzzer: Box<dyn Fuzzer>,

    // HashMap<_, (input_offset, output_offset)>
    buffer_mapping: HashMap<Rc<DeclaredConstant>, (usize, usize)>,

    memory_proxy: Option<MemoryProxy>,

    output: String,
}

impl CPPFuzzEnd {
    pub fn new() -> Self {
        Self {
            fuzzer: Box::new(LibFuzzer::default()),
            buffer_mapping: HashMap::new(),
            memory_proxy: None,
            output: "output".to_string(),
        }
    }

    fn reset(&mut self) {
        self.buffer_mapping.clear();
        self.output = "output".to_string();
    }

    pub fn with_memory_proxy(memory_proxy: MemoryProxy) -> Self {
        Self {
            memory_proxy: Some(memory_proxy),
            ..Self::new()
        }
    }

    pub fn with_fuzzer(fuzzer: Box<dyn Fuzzer>) -> Self {
        Self {
            fuzzer,
            ..Self::new()
        }
    }

    /// Necessary C++ class definitions including those corresponding to the SMT sorts `Bool`, `(_ BitVec n)`,
    /// and `(Array (_ BitVec m) (_ BitVec n))`.
    fn class_defines(&self) -> String {
        include_str!("fuzzcommon.cpp").to_string()
    }
}

impl Default for CPPFuzzEnd {
    fn default() -> Self {
        Self::new()
    }
}

impl FuzzEnd for CPPFuzzEnd {
    fn get_memory_proxy(&self) -> Option<MemoryProxy> {
        self.memory_proxy.clone()
    }

    fn invoke_reset(&mut self) {
        self.reset();
    }

    fn translate_memory_proxy(&mut self, memory_proxy: Option<MemoryProxy>) -> String {
        self.memory_proxy = memory_proxy;
        if let Some(memory_proxy) = &self.memory_proxy {
            format!(
                "MemoryProxy {}({}, {});",
                memory_proxy.name(),
                memory_proxy.min_addr,
                memory_proxy.size,
            )
        } else {
            "".to_string()
        }
    }

    fn translate_smt_type(&self, type_: &Type) -> String {
        match type_ {
            Type::BitVec(size) => format!("SMTBitVec<{}>", size),
            Type::BitVecArray {
                domain_width,
                range_width,
                upper_bound,
            } => {
                if upper_bound.is_none() {
                    format!(
                        "SMTConstArray<SMTBitVec<{}>, SMTBitVec<{}>>",
                        *domain_width, *range_width
                    )
                } else {
                    format!(
                        "SMTArray<SMTBitVec<{}>, SMTBitVec<{}>>",
                        *domain_width, *range_width
                    )
                }
            }
            Type::Bool => "SMTBool".to_string(),
        }
    }

    fn translate_smt2c_type_cast(
        &self,
        from: Either<&ValueRef, (&str, &Type)>,
        to: &str,
    ) -> String {
        let to_str = |from: Either<&ValueRef, (&str, &Type)>| -> String {
            match from {
                Either::Left(value_ref) => self.translate_value_ref_to_name(value_ref),
                Either::Right((expr, _)) => expr.to_string(),
            }
        };

        match (
            match from {
                Either::Left(ref_) => ref_.type_(),
                Either::Right((_, t)) => t.clone(),
            },
            to,
        ) {
            (
                Type::BitVec(_size),
                "char" | "short" | "int" | "long" | "long long" | "unsigned char"
                | "unsigned short" | "unsigned int" | "unsigned long" | "unsigned long long",
            ) => {
                format!("static_cast<{}>({}.raw_value())", to, to_str(from))
            }
            (
                Type::BitVec(_size),
                "char*"
                | "short*"
                | "int*"
                | "long*"
                | "long long*"
                | "unsigned char*"
                | "const char*"
                | "const short*"
                | "const int*"
                | "const long*"
                | "const long long*"
                | "const unsigned char*"
                | "void*"
                | "char *"
                | "short *"
                | "int *"
                | "long *"
                | "long long *"
                | "unsigned char *"
                | "const char *"
                | "const short *"
                | "const int *"
                | "const long *"
                | "const long long *"
                | "const unsigned char *"
                | "void *",
            ) => {
                format!(
                    "(({}) {}.proxy_addr({}.raw_value()))",
                    to,
                    self.get_memory_proxy().unwrap().name(),
                    to_str(from)
                )
            }
            (Type::BitVec(..), _) => unimplemented!("Unsupported cast from BitVec to {}", to),
            (Type::BitVecArray { .. }, _) => todo!(),
            (Type::Bool, "bool") => format!("static_cast<{}>({})", to, to_str(from)),
            (Type::Bool, _) => unimplemented!("Unsupported cast from Bool to {}", to),
        }
    }

    fn translate_c2smt_type_cast(
        &self,
        from: (Either<&ValueRef, &str>, &str),
        to: &Type,
    ) -> String {
        let to_str = |from: Either<&ValueRef, &str>| -> String {
            match from {
                Either::Left(value_ref) => self.translate_value_ref_to_name(value_ref),
                Either::Right(expr) => expr.to_string(),
            }
        };

        match (from.1, to) {
            (
                "char" | "short" | "int" | "long" | "long long" | "unsigned char"
                | "unsigned short" | "unsigned int" | "unsigned long" | "unsigned long long",
                Type::BitVec(..),
            ) => {
                format!(
                    "{}((uint64_t) {})",
                    self.translate_smt_type(to),
                    to_str(from.0)
                )
            }
            (
                "const char *"
                | "const short *"
                | "const int *"
                | "const long *"
                | "const long long *"
                | "const unsigned char *"
                | "const char*"
                | "const short*"
                | "const int*"
                | "const long*"
                | "const long long*"
                | "const unsigned char*"
                | "char *"
                | "short *"
                | "int *"
                | "long *"
                | "long long *"
                | "unsigned char *"
                | "void *"
                | "char*"
                | "short*"
                | "int*"
                | "long*"
                | "long long*"
                | "unsigned char*"
                | "void*",
                Type::BitVec(..),
            ) => {
                format!(
                    "{}({}.original_addr((uint64_t) {}))",
                    self.translate_smt_type(to),
                    self.get_memory_proxy().unwrap().name(),
                    to_str(from.0)
                )
            }
            (_, Type::BitVec(..)) => unimplemented!("Unsupported cast from {} to BitVec", from.1),
            ("bool", Type::Bool) => format!(
                "static_cast<{}>({})",
                self.translate_smt_type(to),
                to_str(from.0)
            ),
            (_, Type::Bool) => unimplemented!("Unsupported cast from {} to Bool", from.1),
            (_, Type::BitVecArray { .. }) => todo!(),
        }
    }

    fn translate_literal_value(&self, lit: &LiteralValue) -> String {
        match lit {
            LiteralValue::BitVecValue(_, bytes, ..) => {
                let mut byte_str = Vec::with_capacity(bytes.len());
                for byte in bytes.iter() {
                    byte_str.push(format!("{:02x}", byte));
                }
                format!(
                    "{}::from_hex_str((const char*) \"{}\")",
                    self.translate_smt_type(&lit.type_()),
                    byte_str.join("")
                )
            }
            LiteralValue::BitVecArrayValue(_, _, _) => unreachable!(),
            LiteralValue::BoolValue(v) => {
                format!(
                    "static_cast<{}>({})",
                    self.translate_smt_type(&lit.type_()),
                    if *v { "true" } else { "false" }
                )
            }
        }
    }

    fn translate_value_ir(&self, ir: &IRRef) -> String {
        let type_ = ir.borrow().type_();
        let operands = ir.borrow().operands().to_vec();
        let kind = ir.borrow().kind().clone();
        use IRKind::*;
        let body = match_template! {
            UNARY_OP = [Not => "!", BVNot => "~", BVNeg => "-"],
            BINARY_OP = [And => "&&", Or => "||", Eq => "==", Ne => "!=", BVAnd => "&",
                         BVOr => "|", BVAdd => "+", BVSub => "-", BVMul => "*", BVUDiv => "/",
                         BVURem => "%", BVULt => "<", BVComp => "==", BVULe => "<=", BVUGt => ">",
                         BVUGe => ">="],
            UNARY_METHOD = [BVShL => "shl", BVLShR => "lshr", BVSDiv => "sdiv", BVSRem => "srem",
                            BVSMod => "smod", BVAShR => "ashr", BVSLt => "slt", BVSLe => "sle",
                            BVSGt => "sgt", BVSGe => "sge", Select => "select"],
            UNARY_TEMPLATE = [Repeat => "repeat", ZeroExtend => "zero_ext", SignExtend => "sign_ext",
                              RotateLeft => "rotate_left", RotateRight => "rotate_right"],
            match &kind {
                UNARY_OP => format!("{}{}", UNARY_OP, self.translate_value_ref_to_name(&operands[0])),
                BINARY_OP => format!("{} {} {}", self.translate_value_ref_to_name(&operands[0]), BINARY_OP, self.translate_value_ref_to_name(&operands[1])),
                UNARY_METHOD => format!("{}.{}({})", &operands[0], UNARY_METHOD, &operands[1]),
                UNARY_TEMPLATE(index) => format!("{}.template {}<{}>()", self.translate_value_ref_to_name(&operands[0]), UNARY_TEMPLATE, *index),
                ConstantRef(unknown) => self.translate_unknown_to_name(unknown),
                Literal{ literal } => self.translate_literal_value(literal),
                Bool2BV => format!("SMTBitVec<1>::from_bool({})", self.translate_value_ref_to_name(&operands[0])),
                BV2Bool => format!("{}.raw_bool()", &operands[0]),
                Ite => format!("({}) ? ({}) : ({})", self.translate_value_ref_to_name(&operands[0]), self.translate_value_ref_to_name(&operands[1]), self.translate_value_ref_to_name(&operands[2])),
                CallCBFunction(cb) => {
                    let func_name = &cb.id;
                    let mut reified_args = Vec::new();
                    for (arg, param) in operands.iter().zip(cb.params.iter()) {
                        assert_eq!(param.0, arg.type_());
                        let tmp = self.translate_smt2c_type_cast(Either::Left(arg), &param.1);
                        reified_args.push(tmp);
                    }
                    let tmp = format!("{}({})", func_name, reified_args.join(", "));
                    let (return_smt_t, return_ct) = &cb.return_smt_and_c_type;
                    self.translate_c2smt_type_cast((Either::Right(&tmp), return_ct), return_smt_t)
                }
                Concat => format!("{}.concat({})", self.translate_value_ref_to_name(&operands[1]), self.translate_value_ref_to_name(&operands[0])),
                Extract(from, to) => format!("{}.template extract<{}, {}>()", self.translate_value_ref_to_name(&operands[0]), *from, *to),
                Store => format!("{}.store({}, {})", self.translate_value_ref_to_name(&operands[0]), self.translate_value_ref_to_name(&operands[1]), self.translate_value_ref_to_name(&operands[2])),
                ConstBVArray(domain_size, range_size) => format!("SMTConstArray<SMTBitVec<{}>, SMTBitVec<{}>>({})", *domain_size, *range_size, self.translate_value_ref_to_name(&operands[0])),
                Alias => self.translate_value_ref_to_name(&operands[0]),
                Check | Memset(_, _) | WriteBack(_) => unreachable!(),
            }
        };
        let var_name = self.translate_value_ref_to_name(&ir.borrow().value_ref().unwrap());
        format!(
            "{} {} = {};",
            self.translate_smt_type(&type_),
            var_name,
            body
        )
    }

    fn translate_check_ir(&self, check: &IRRef) -> String {
        let to_check = check.borrow().operands()[0].clone();
        assert!(Type::Bool == to_check.type_());
        format!(
            "if (!{}) return 0;",
            self.translate_value_ref_to_name(&to_check)
        )
    }

    fn translate_writeback_ir(&self, const_alias: &DeclaredConstant, value: &ValueRef) -> String {
        match const_alias.type_ {
            Type::BitVec(size) => {
                // assert!(size % 8 == 0 || size == 1);
                let (_, out_offset) = self.buffer_mapping.get(const_alias).unwrap().clone();
                assert_eq!(0, out_offset % 8);
                let Type::BitVec(sz) = value.type_() else {
                    unreachable!()
                };

                assert_eq!(sz, size);

                format!(
                    "{}.record_bitvec({}, {});",
                    self.output,
                    out_offset,
                    self.translate_value_ref_to_name(value),
                )
            }
            Type::BitVecArray {
                domain_width: _,
                range_width,
                upper_bound,
            } => {
                let Type::BitVec(sz) = value.type_() else {
                    unreachable!()
                };
                if let Some(ub) = upper_bound {
                    assert!(sz <= range_width * (ub as usize + 1));
                }
                assert!(range_width % 8 == 0);
                assert!(sz % 8 == 0);

                let (_, out_offset) = self.buffer_mapping.get(const_alias).unwrap().clone();
                assert_eq!(0, out_offset % 8);
                format!(
                    "{}.record_bitvec({}, {});",
                    self.output,
                    out_offset,
                    self.translate_value_ref_to_name(value),
                )
            }
            Type::Bool => {
                let (_, out_offset) = self.buffer_mapping.get(const_alias).unwrap().clone();
                assert_eq!(0, out_offset % 8);
                format!(
                    "{}.record_bool({}, {});",
                    self.output,
                    out_offset,
                    self.translate_value_ref_to_name(value),
                )
            }
        }
    }

    fn translate_memset_ir(&self, addr: &u64, expr: Either<&ValueRef, &str>) -> String {
        match expr {
            Either::Left(expr) => {
                format!(
                    "{}.memset({}, {});",
                    self.get_memory_proxy().unwrap().name(),
                    *addr,
                    self.translate_value_ref_to_name(&expr)
                )
            }
            Either::Right(hex_bytes) => {
                format!(
                    "{}.memset({}, \"{}\");",
                    self.get_memory_proxy().unwrap().name(),
                    *addr,
                    hex_bytes
                )
            }
        }
    }

    fn translate_construct_input(&self, _unknowns: &[Rc<DeclaredConstant>]) -> Vec<String> {
        let mut lines = Vec::new();
        for (unknown, (in_offset, _)) in self.buffer_mapping.iter() {
            let name = self.translate_unknown_to_name(&unknown);
            let vbytes = unknown.virtual_bytes();
            let (ty, body) = match &unknown.type_ {
                Type::BitVec(n) => {
                    let r = (
                        self.translate_smt_type(&unknown.type_),
                        format!(
                            "{}.read_bv<{}>({}, {{{}}})",
                            self.input_buffer(),
                            n,
                            in_offset,
                            vbytes.iter().map(|b| format!("{}", b)).join(", ")
                        ),
                    );
                    r
                }
                Type::BitVecArray {
                    domain_width,
                    range_width,
                    upper_bound,
                } => {
                    let r = (
                        self.translate_smt_type(&unknown.type_),
                        format!(
                            "{}.read_bv_arr<{}, {}>({}, {}, {{{}}})",
                            self.input_buffer(),
                            *domain_width,
                            *range_width,
                            in_offset,
                            upper_bound.unwrap(),
                            vbytes.iter().map(|b| format!("{}", b)).join(", ")
                        ),
                    );
                    r
                }
                Type::Bool => {
                    let r = (
                        self.translate_smt_type(&unknown.type_),
                        format!(
                            "{}.read_bool({}, {{{}}})",
                            self.input_buffer(),
                            in_offset,
                            vbytes.iter().map(|b| format!("{}", b)).join(", ")
                        ),
                    );
                    r
                }
            };
            lines.push(format!("{} {} = {};", ty, name, body));
        }
        lines
    }

    fn translate_cb_function_declaration(&self, _cb_function: &KRPKCBFunctionDecl) -> String {
        // We currently use include headers to include all cb functions.
        // TODO: Change this.
        return "".to_string();
    }

    fn common_heads(&self, fuzzer_id: &str, fuzz_program: &FuzzProgram) -> String {
        assert_eq!("cpp:libfuzzer", fuzzer_id); // TODO: Support other fuzzers?
        let (input_size_in_bits, output_size_in_bits) =
            fuzz_program
                .unknowns()
                .fold((0usize, 0usize), |(in_acc, out_acc), e| {
                    let t1 = in_acc + {
                        let tmp = e.size_in_bytes();
                        let virtual_bytes = e.virtual_bytes().len();
                        (tmp - virtual_bytes) * 8
                    };
                    let t2 = out_acc + e.size_in_bytes() * 8;
                    (t1, t2)
                });
        let input_size_in_bytes =
            input_size_in_bits / 8 + if input_size_in_bits % 8 == 0 { 0 } else { 1 };
        assert_eq!(0, output_size_in_bits % 8);
        let output_size_in_bytes = output_size_in_bits / 8;
        format!(
            r##"
            |#include <stdint.h>
            |#include <stdlib.h>
            |#include <string.h>
            |#include <math.h>
        "##
        )
        .trim_margin()
        .unwrap()
            + "\n"
            + self.class_defines().as_str()
            + "\n"
            + &format!(
                r##"
            |extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
            |{{
            |    if (size != {})
            |    {{
            |        return 0;
            |    }}
            |    InputBuffer input_buffer = InputBuffer(data, size);
            |    Output {} = Output("./output/{}", {});
        "##,
                input_size_in_bytes,
                self.output,
                self.fuzzer().output_file(),
                output_size_in_bytes,
            )
            .trim_margin()
            .unwrap()
    }

    fn common_tails(&self, fuzzer_id: &str, _fuzz_program: &FuzzProgram) -> String {
        assert_eq!("cpp:libfuzzer", fuzzer_id); // TODO: Support other fuzzers?
        format!(
            r##"
        |    // Fuzzing target
        |    {}.dump();
        |    abort();
        |}}
        "##,
            self.output
        )
        .trim_margin()
        .unwrap()
    }

    fn fuzzer(&self) -> &dyn Fuzzer {
        self.fuzzer.as_ref()
    }

    fn fuzzer_mut(&mut self) -> &mut dyn Fuzzer {
        self.fuzzer.as_mut()
    }

    fn set_model_extraction(&mut self, fuzz_program: &FuzzProgram) {
        let mut in_offset = 0;
        let mut out_offset = 0;
        for unknown in fuzz_program.unknowns() {
            self.buffer_mapping
                .insert(unknown.clone(), (in_offset, out_offset));
            let sz = unknown.size_in_bytes();
            let actual_sz = sz - unknown.virtual_bytes().len();
            in_offset += actual_sz * 8;
            out_offset += sz * 8;
        }
    }

    fn extract_model(&self, buffer: &[u8]) -> super::response::Model {
        let mut assignments = HashMap::with_capacity(self.buffer_mapping.len());
        for (unknown, (_, out_offset)) in self.buffer_mapping.iter() {
            fn get_value(buffer: &[u8], offset: usize, type_: &Type) -> LiteralValue {
                assert_eq!(0, offset % 8);
                let byte_offset = offset / 8;
                match &type_ {
                    Type::BitVec(size) => {
                        // assert!(0 == size % 8 || 1 == *size);
                        let sz = size / 8 + if size % 8 == 0 { 0 } else { 1 };
                        let mut bytes = Vec::with_capacity(sz);
                        for byte in buffer[byte_offset..byte_offset + sz].iter() {
                            bytes.push(*byte);
                        }
                        LiteralValue::BitVecValue(*size, bytes)
                    }
                    Type::BitVecArray {
                        domain_width,
                        range_width,
                        upper_bound,
                    } => {
                        let upper_bound = upper_bound.unwrap();
                        let mut bit_vecs = Vec::with_capacity(upper_bound as usize);
                        for i in 0..=upper_bound {
                            let value = get_value(
                                buffer,
                                offset + (i as usize) * *range_width,
                                &Type::BitVec(*range_width),
                            );
                            bit_vecs.push(value);
                        }
                        LiteralValue::BitVecArrayValue(
                            *domain_width,
                            *range_width,
                            bit_vecs
                                .iter()
                                .map(|lit| match lit {
                                    LiteralValue::BitVecValue(_, bytes) => bytes.clone(),
                                    _ => unreachable!(),
                                })
                                .collect_vec(),
                        )
                    }
                    Type::Bool => LiteralValue::BoolValue(buffer[byte_offset] == 0x1),
                }
            }
            let value = get_value(buffer, *out_offset, &unknown.type_);
            assignments.insert(unknown.clone(), value);
        }
        super::response::Model::with_values(assignments)
    }
}

#[cfg(test)]
mod test {
    use crate::fuzzend::Solution;
    use crate::smt2fuzz::SMT2Fuzz;
    use crate::smtanalyze::Analyzer;
    use crate::smtparser::parse_str;

    use super::*;

    #[test]
    fn test_core_simple1() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (assert (= x false))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |x := false
            "#
            .trim_margin()
            .unwrap(),
            solution_representation.trim()
        );
    }

    #[test]
    fn test_core_simple2() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (assert (= x true))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |x := true
            "#
            .trim_margin()
            .unwrap(),
            solution_representation.trim()
        );
    }

    #[test]
    fn test_core_simple3() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (declare-const y Bool)
            | (assert (and x y))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |x := true
                |y := true
            "#
            .trim_margin()
            .unwrap(),
            solution_representation.trim()
        );
    }

    #[test]
    fn test_core_simple4() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (declare-const y Bool)
            | (declare-const z Bool)
            | (assert (and x y z))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |x := true
                |y := true
                |z := true
            "#
            .trim_margin()
            .unwrap(),
            solution_representation.trim()
        );
    }

    #[test]
    fn test_core_simple5() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (declare-const y Bool)
            | (declare-const z Bool)
            | (assert (= x y z))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);
        assert!(
            r#"
                |sat:
                |x := true
                |y := true
                |z := true
            "#
            .trim_margin()
            .unwrap()
                == solution_representation.trim()
                || r#"
                    |sat:
                    |x := false
                    |y := false
                    |z := false
                "#
                .trim_margin()
                .unwrap()
                    == solution_representation.trim()
        )
    }

    #[test]
    fn test_core_simple6() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (declare-const y Bool)
            | (assert (distinct x y))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_representation = format!("{}", solution);

        assert!(
            r#"
                |sat:
                |x := false
                |y := true
            "#
            .trim_margin()
            .unwrap()
                == solution_representation.trim()
                || r#"
                    |sat:
                    |x := true
                    |y := false
                "#
                .trim_margin()
                .unwrap()
                    == solution_representation.trim()
        );
    }

    #[test]
    fn test_core_ite() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (declare-const y Bool)
            | (declare-const z Bool)
            | (assert (ite x (xor x z) y))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let Solution::Sat(model) = solution else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, model.size());
        let mut xv = None;
        let mut yv = None;
        let mut zv = None;
        for (constant, value) in model.iter() {
            match constant.name.as_str() {
                "x" => {
                    xv = Some(if let LiteralValue::BoolValue(bv) = value {
                        *bv
                    } else {
                        panic!("x is not a bool")
                    })
                }
                "y" => {
                    yv = Some(if let LiteralValue::BoolValue(bv) = value {
                        *bv
                    } else {
                        panic!("y is not a bool")
                    })
                }
                "z" => {
                    zv = Some(if let LiteralValue::BoolValue(bv) = value {
                        *bv
                    } else {
                        panic!("z is not a bool")
                    })
                }
                _ => unreachable!(),
            }
        }
        let xv = xv.unwrap();
        let yv = yv.unwrap();
        let zv = zv.unwrap();
        assert!(if xv { (xv && !zv) || (!xv && zv) } else { yv })
    }

    #[test]
    fn test_bv_simple() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x (_ BitVec 8))
            | (assert (= x #x01))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |x := #x01
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_array_simple() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
            | (assert (= (select arr #x00) #x02))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |arr := [#x00 => #x02, ]
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_array_simple2() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const arr (Array (_ BitVec 32) (_ BitVec 8)))
            | (assert (and (= (select arr #x00000000) #x01) (= (select arr #x00000001) #x02)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |arr := [#x00000000 => #x01, #x00000001 => #x02, ]
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_const_array_simple() {
        let src = r#"
            | (set-logic ALL)
            | (declare-const x (_ BitVec 8))
            | (assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x04) #x03) x))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |x := #x04
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_not() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (not (= a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := false
            |b := true
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := true
            |b := false
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_imply() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (=> a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := false
            |b := true
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := false
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
                || r#"
            |sat:
            |a := true
            |b := true
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_and() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (and a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := true
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
        );
    }

    #[test]
    fn test_or() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (or a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := true
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := true
            |b := false
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := true
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_xor() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (xor a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := false
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := true
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }
    #[test]
    fn test_equal() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (= a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := true
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := false
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }
    #[test]
    fn test_distinct() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b Bool)
            |(assert (distinct a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := false
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := true
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_ite() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(declare-const b (_ BitVec 8))
            |(assert (= b (ite a #x01 #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        cpp_fuzzend.set_fuzzer_option("max_time_in_milliseconds", "2000");
        // XXX: Have to do this since some times the default timeout is too short to get a solution.
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
            |sat:
            |a := true
            |b := #x01
        "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
            |sat:
            |a := false
            |b := #x00
        "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_concat() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 4))
            |(declare-const b (_BitVec 4))
            |(declare-const c (_BitVec 8))
            |(assert (= c (concat b a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(csz, cv) = solution.value_by_name("c").unwrap() else {
            unreachable!()
        };

        assert_eq!(4, *asz);
        assert_eq!(4, *bsz);
        assert_eq!(8, *csz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        let [cb] = cv.as_slice() else {
            panic!("c is not a single byte")
        };
        assert_eq!(*cb, (*bb << 4) | *ab);
    }

    #[test]
    fn test_bvnot() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvnot #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #xff
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        )
    }

    #[test]
    fn test_bvand() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(declare-const b (_BitVec 8))
            |(declare-const c (_BitVec 8))
            |(assert (= c (bvand a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(csz, cv) = solution.value_by_name("c").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *asz);
        assert_eq!(8, *bsz);
        assert_eq!(8, *csz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        let [cb] = cv.as_slice() else {
            panic!("c is not a single byte")
        };
        assert_eq!(*cb, *ab & *bb);
    }

    #[test]
    fn test_bvor() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(declare-const b (_BitVec 8))
            |(declare-const c (_BitVec 8))
            |(assert (= c (bvor a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(csz, cv) = solution.value_by_name("c").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *asz);
        assert_eq!(8, *bsz);
        assert_eq!(8, *csz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        let [cb] = cv.as_slice() else {
            panic!("c is not a single byte")
        };
        assert_eq!(*cb, *ab | *bb);
    }

    #[test]
    fn test_bvneg() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(declare-const b (_BitVec 8))
            |(assert (= b (bvneg a )))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(2, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *asz);
        assert_eq!(8, *bsz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        assert_eq!(*bb, (-(*ab as i16)) as u8);
    }

    #[test]
    fn test_bvadd() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(declare-const b (_BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvadd a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(csz, cv) = solution.value_by_name("c").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *asz);
        assert_eq!(8, *bsz);
        assert_eq!(8, *csz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        let [cb] = cv.as_slice() else {
            panic!("c is not a single byte")
        };
        assert_eq!(*cb, ab.wrapping_add(*bb));
    }

    #[test]
    fn test_bvmul() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(declare-const b (_BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvmul a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(3, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        let LiteralValue::BitVecValue(csz, cv) = solution.value_by_name("c").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *asz);
        assert_eq!(8, *bsz);
        assert_eq!(8, *csz);
        let [ab] = av.as_slice() else {
            panic!("a is not a single byte")
        };
        let [bb] = bv.as_slice() else {
            panic!("b is not a single byte")
        };
        let [cb] = cv.as_slice() else {
            panic!("c is not a single byte")
        };
        assert_eq!(*cb, ab.wrapping_mul(*bb));
    }

    #[test]
    fn test_bvudiv() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= #x02 (bvudiv a #x02)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
                |sat:
                |a := #x04
            "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
                |sat:
                |a := #x05
            "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_bvudiv_zero() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvudiv #x02 #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x01
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvurem() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= #x01 (bvurem a #x80)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert!(
            r#"
                |sat:
                |a := #x81
            "#
            .trim_margin()
            .unwrap()
                == solution_repr.trim()
                || r#"
                |sat:
                |a := #x01
            "#
                .trim_margin()
                .unwrap()
                    == solution_repr.trim()
        );
    }

    #[test]
    fn test_bvurem_zero() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvurem #x02 #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x02
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvshl() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvshl #x02 #x01)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x04
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvlshr() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvlshr #xFF #x01)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x7f
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvult() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvult #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvcomp() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 1))
            |(assert (= a (bvcomp #xFA #xFA)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x01
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvcomp_ne() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 1))
            |(assert (= a (bvcomp #xFF #xFA)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x00
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsub() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= #x03 (bvsub a #x02)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x05
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsdiv() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsdiv #xFE #xFF)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x02
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsdiv_zero() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsdiv #xFE #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x01
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsrem() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsrem #xFF #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #xff
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsrem_zero() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsrem #xFF #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #xff
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsmod() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsmod #xFF #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x01
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvsmod_zero() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvsmod #xFE #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #x02
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvashr() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 8))
            |(assert (= a (bvashr #xAF #x01)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
                |sat:
                |a := #xd7
            "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_bvule() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvule #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvugt() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvugt #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := false
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvuge() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvugt #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := false
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvslt() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvslt #xFE #x02)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvsle() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvsle #xFE #x02)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvsgt() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvsgt #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_bvsge() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a Bool)
            |(assert (= a (bvsge #x02 #xFE)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        assert_eq!(
            r#"
            |sat:
            |a := true
        "#
            .trim_margin()
            .unwrap(),
            format!("{}", solution).trim()
        );
    }

    #[test]
    fn test_extract() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 16))
            |(assert (= ((_ extract 10 3) a) #x03))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(1, solution.size());
        let LiteralValue::BitVecValue(asz, av) = solution.value_by_name("a").unwrap() else {
            unreachable!()
        };
        assert_eq!(16, *asz);
        let [ab0, ab1] = av.as_slice() else {
            panic!("a is not two bytes")
        };
        let ab = u16::from_le_bytes([*ab0, *ab1]);
        assert_eq!(0x0003, (ab & (0xFF << 3)) >> 3);
    }

    #[test]
    fn test_repeat() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 4))
            |(assert (= #xFF ((_ repeat 2) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x0f
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_zero_extend() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 16))
            |(assert (= a ((_ zero_extend 8) #xFF)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x00ff
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_sign_extend() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 16))
            |(assert (= a ((_ sign_extend 8) #xFF)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #xffff
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_rotate_left() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ rotate_left 2) #x7F)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |b := #xfd
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_rotate_right() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ rotate_right 2) #x7F)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |b := #xdf
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_select() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            |(assert (= #x02 (select a #x01)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(1, solution.size());
        let LiteralValue::BitVecArrayValue(dsz, rsz, av) = solution.value_by_name("a").unwrap()
        else {
            unreachable!()
        };
        assert_eq!(8, *dsz);
        assert_eq!(8, *rsz);
        let [ab0, ab1] = av.as_slice() else {
            panic!("a is not two arrays")
        };
        assert_eq!(1, ab0.len());
        assert_eq!(1, ab1.len());
        assert_eq!(0x02, ab1[0]);
    }

    #[test]
    fn test_store() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            |(declare-const b (_ BitVec 8))
            |(assert (= b (select (store a #x00 #x03) #x00)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(solution) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        assert_eq!(2, solution.size());
        assert!(solution.value_by_name("a").is_some());
        let LiteralValue::BitVecValue(bsz, bv) = solution.value_by_name("b").unwrap() else {
            unreachable!()
        };
        assert_eq!(8, *bsz);
        assert_eq!(0x03, bv[0]);
    }

    #[test]
    fn test_const_bvarray() {
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(assert (= #x03 (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) a) #x08)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let solution = cpp_fuzzend.solve(&fuzz_program).unwrap();
        let solution_repr = format!("{}", solution);
        assert_eq!(
            r#"
            |sat:
            |a := #x03
        "#
            .trim_margin()
            .unwrap(),
            solution_repr.trim()
        );
    }

    #[test]
    fn test_pointer() {
        let src = r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(define-ctype int (_ BitVec 64))
            |(define-ctype char* (_ BitVec 64))
            |(define-ctype |const char*| (_ BitVec 64))
            |(declare-cb strchr (|const char*| int) char*)
            |(alloc #x0000000000007ff0 1 #x61)
            |(alloc #x0000000000007ff1 1 #x00)
            |(declare-const a (_ BitVec 64))
            |(assert (= #x0000000000007ff0 (strchr #x0000000000007ff0 a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(model) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        let a_value = model.value_by_name("a").unwrap();
        let LiteralValue::BitVecValue(_, bytes) = a_value else {
            panic!("a is not a bitvec")
        };
        assert_eq!(8, bytes.len());
        assert_eq!(0x61, bytes[0]);
    }

    #[test]
    fn test_pointer_hex_str() {
        let src = r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(define-ctype int (_ BitVec 64))
            |(define-ctype char* (_ BitVec 64))
            |(define-ctype |const char*| (_ BitVec 64))
            |(declare-cb strchr (|const char*| int) char*)
            |(alloc #x0000000000007ff0 2 "6100")
            |(declare-const a (_ BitVec 64))
            |(assert (= #x0000000000007ff0 (strchr #x0000000000007ff0 a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::new().compile(&analyzed).unwrap();
        let mut cpp_fuzzend = CPPFuzzEnd::new();
        let Solution::Sat(model) = cpp_fuzzend.solve(&fuzz_program).unwrap() else {
            panic!("Solution is not sat")
        };
        let a_value = model.value_by_name("a").unwrap();
        let LiteralValue::BitVecValue(_, bytes) = a_value else {
            panic!("a is not a bitvec")
        };
        assert_eq!(8, bytes.len());
        assert_eq!(0x61, bytes[0]);
    }
}
