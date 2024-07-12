use crate::fuzzend::Solution as RawSolution;
use crate::fuzzend::{CPPFuzzEnd, FuzzEnd};
use crate::hir::SMTScript;
use crate::smt2fuzz::{SMT2Fuzz, SMT2FuzzError};
use crate::smtanalyze::{Analyzer, AnalyzerError, KRPKIdentifier, KRPKQualIdentifier, KRPKTerm};

#[derive(Debug)]
pub enum SolverError {
    AnalyzerError(AnalyzerError),
    SMT2FuzzError(SMT2FuzzError),
    FuzzEndError(i32),
}

pub struct FuzzSolver {
    analyzer: Analyzer,
    smt2fuzz: SMT2Fuzz,
    fuzzend: Box<dyn FuzzEnd>,
}

impl FuzzSolver {
    pub fn new() -> Self {
        Self {
            analyzer: Analyzer::new(),
            smt2fuzz: SMT2Fuzz::new(),
            fuzzend: Box::new(CPPFuzzEnd::new()),
        }
    }

    pub fn set_fuzzer_option(&mut self, option: &str, value: &str) {
        self.fuzzend.set_fuzzer_option(option, value);
    }

    pub fn get_fuzzer_option(&self, option: &str) -> Option<String> {
        self.fuzzend.get_fuzzer_option(option)
    }

    // TODO: Return `hir::response` responses instead of raw solution.
    pub fn solve(&mut self, smt_script: &SMTScript) -> Result<RawSolution, SolverError> {
        let analyzed = self
            .analyzer
            .analyze(smt_script)
            .map_err(|err| SolverError::AnalyzerError(err))?;

        // Fast path
        // If there is false in a series of conjunctive normal forms, it currently returns Unknow directly.
        // In fact, it should be UnSat. We plan to change it later.
        let sorted_terms = analyzed.assertions();
        for term in sorted_terms {
            let item = &term.item;
            if let KRPKTerm::Identifier(KRPKQualIdentifier::Simple(KRPKIdentifier::Symbol(ref s))) =
                item
            {
                if s == "false" {
                    return Ok(RawSolution::Unknown);
                }
            }
        }

        // XXX: Cycle in the DAG?
        let fuzz_program = self
            .smt2fuzz
            .compile(&analyzed)
            .map_err(|err| SolverError::SMT2FuzzError(err))?;

        let fuzz_result = self
            .fuzzend
            .solve(&fuzz_program)
            .map_err(|err| SolverError::FuzzEndError(err))?;
        self.fuzzend.invoke_reset();

        Ok(fuzz_result)
    }
} //
