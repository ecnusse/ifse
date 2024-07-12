use std::fmt;
use std::rc::Rc;

use either::Either;

use crate::mir::{
    DeclaredConstant, FuzzProgram, IRKind, IRRef, LiteralValue, MemoryProxy, Type, ValueRef,
};
use crate::smtanalyze::KRPKCBFunctionDecl;

use super::response::Model;

#[derive(Debug, Clone)]
pub enum FuzzResult {
    Success(Vec<u8>),
    Timeout,
}

pub trait Fuzzer {
    fn fuzz(&self, program_text: &str) -> Result<FuzzResult, i32>;
    fn id(&self) -> &str;
    fn set_option(&mut self, option: &str, value: &str);
    fn get_option(&self, option: &str) -> Option<String>;

    fn output_file(&self) -> String {
        "fuzz_out".to_string()
    }
}

#[derive(Debug, Clone)]
pub enum Solution {
    Unknown,
    Sat(Model),
}

impl fmt::Display for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Solution::Unknown => write!(f, "unknown"),
            Solution::Sat(model) => write!(f, "sat:\n{}", model),
        }
    }
}

/// A [`FuzzEnd`] specifies a fuzzer, transforms a fuzz program to actual programs (written in the programming
/// language required by that fuzzer), and invokes the fuzzer to solve the program.
pub trait FuzzEnd {
    fn translate_value_ref_to_name(&self, value_ref: &ValueRef) -> String {
        format!("{}", value_ref)
    }

    fn invoke_reset(&mut self);

    fn translate_unknown_to_name(&self, unknown: &DeclaredConstant) -> String {
        unknown.name.clone()
    }

    fn get_memory_proxy(&self) -> Option<MemoryProxy>;

    fn translate_memory_proxy(&mut self, memory_proxy: Option<MemoryProxy>) -> String;

    /// Convert SMT type to a string.
    fn translate_smt_type(&self, type_: &Type) -> String;

    /// Cast a expr ref with a SMT type to a C type. Return a string that represents such a cast.
    fn translate_smt2c_type_cast(&self, from: Either<&ValueRef, (&str, &Type)>, to: &str)
        -> String;

    /// Cast a expr ref with a C type (`from`) to a SMT type. Return a string that represents such a cast.
    fn translate_c2smt_type_cast(&self, from: (Either<&ValueRef, &str>, &str), to: &Type)
        -> String;

    fn translate_literal_value(&self, lit: &LiteralValue) -> String;
    fn translate_value_ir(&self, expr: &IRRef) -> String;

    /// We assume that all check stmts have been merged to one.
    fn translate_check_ir(&self, check: &IRRef) -> String;

    fn translate_writeback_ir(&self, const_alias: &DeclaredConstant, value: &ValueRef) -> String;

    fn translate_ir(&self, ir: &IRRef) -> String {
        match ir.borrow().kind() {
            IRKind::Check => self.translate_check_ir(ir),
            IRKind::Memset(addr, bytes) => {
                if let Some(bytes) = bytes {
                    self.translate_memset_ir(addr, Either::Right(bytes))
                } else {
                    self.translate_memset_ir(addr, Either::Left(&ir.borrow().operands()[0]))
                }
            }
            IRKind::WriteBack(unknown) => {
                self.translate_writeback_ir(unknown, &ir.borrow().operands()[0])
            }
            _ => self.translate_value_ir(ir),
        }
    }

    fn translate_memset_ir(&self, addr: &u64, expr: Either<&ValueRef, &str>) -> String;

    fn input_buffer(&self) -> String {
        "input_buffer".to_string()
    }

    fn translate_construct_input(&self, unknowns: &[Rc<DeclaredConstant>]) -> Vec<String>;

    fn translate_cb_function_declaration(&self, cb_function: &KRPKCBFunctionDecl) -> String;

    // Sanitize inputs here.
    fn common_heads(&self, fuzzer_id: &str, fuzz_program: &FuzzProgram) -> String;

    // Hit the target here.
    fn common_tails(&self, fuzzer_id: &str, fuzz_program: &FuzzProgram) -> String;

    fn fuzzer(&self) -> &dyn Fuzzer;

    fn fuzzer_mut(&mut self) -> &mut dyn Fuzzer;

    fn set_model_extraction(&mut self, fuzz_program: &FuzzProgram);
    fn extract_model(&self, buffer: &[u8]) -> Model;

    fn solve(&mut self, fuzz_program: &FuzzProgram) -> Result<Solution, i32> {
        self.set_model_extraction(fuzz_program);

        let mut program_text: Vec<String> = Vec::new();
        program_text.push(self.common_heads(self.fuzzer().id(), fuzz_program));

        program_text.append(
            &mut self.translate_construct_input(
                fuzz_program
                    .unknowns()
                    .map(|e| e.clone())
                    .collect::<Vec<_>>()
                    .as_slice(),
            ),
        );
        program_text.push(self.translate_memory_proxy(fuzz_program.memory_proxy()));

        fuzz_program.visit(|ir| {
            program_text.push(self.translate_ir(&ir));
        });

        program_text.push(self.common_tails(self.fuzzer().id(), fuzz_program));

        let fuzz_result = self.fuzzer().fuzz(&program_text.join("\n"))?;
        match fuzz_result {
            FuzzResult::Timeout => Ok(Solution::Unknown),
            FuzzResult::Success(buffer) => {
                let model = self.extract_model(&buffer);
                Ok(Solution::Sat(model))
            }
        }
    }

    fn set_fuzzer_option(&mut self, option: &str, value: &str) {
        self.fuzzer_mut().set_option(option, value);
    }

    fn get_fuzzer_option(&self, option: &str) -> Option<String> {
        self.fuzzer().get_option(option)
    }
}
