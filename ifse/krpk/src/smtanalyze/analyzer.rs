use either::Either;
use itertools::Itertools;
use std::collections::{BTreeMap, HashMap};

use super::{
    CTypeError, FunctionDeclarationError, KRPKArch, KRPKCBFunctionDecl, KRPKFunctionDeclaration,
    KRPKMatchCase, KRPKQualIdentifier, KRPKSpecConstant, KRPKTerm, Sorted,
};
use super::{KRPKEnvironment, KRPKGroundSort, KRPKIdentifier, KRPKLogic};

use crate::hir::{Binary, Command, Hexadecimal, Keyword, MemoryCell, SMTOption, SMTScript, Symbol};
use crate::smtanalyze::{AllocError, FunctionError, KRPKFunction, KRPKIndex};

use log::{info, warn};

/// Emulate the solver modes defined on page 52 of SMT-LIB Standard 2.6. No `Sat` or `Unsat` since we don't actually solve at this step.
/// [`EmulatedSolverMode::AfterCheck`] covers both the two.
#[derive(Clone, PartialEq, Eq, Debug, Hash, Copy)]
pub enum EmulatedSolverMode {
    Start,
    Assert,
    AfterCheck,
    Exit,
}

#[derive(Clone, PartialEq, Debug)]
pub enum AnalyzerError {
    UnknownLogic(String),
    UnknownArch(String),
    DisallowedCommand(EmulatedSolverMode, String),
    FunctionDeclarationError(FunctionDeclarationError),
    UndefinedSymbol(KRPKIdentifier),
    SignatureMismatch(KRPKFunctionDeclaration, Vec<KRPKGroundSort>),
    CBSignatureMismatch(KRPKCBFunctionDecl),
    SortMismatch {
        expected: KRPKGroundSort,
        actual: KRPKGroundSort,
    },
    CTypeDeclarationError(CTypeError),
    ArchUnset,
    AllocOverlap(u64, usize, u64),
    AllocOverflow(u64, usize, KRPKGroundSort),
    AllocUnsized(u64, KRPKGroundSort),
    AllocSizeMismatch(u64, u64),
    MultipleSetArch,
}

impl From<FunctionError> for AnalyzerError {
    fn from(_value: FunctionError) -> Self {
        todo!()
    }
}

/// [`Sorter`] derives a sort for each semantic objects according to the rules listed
/// on page 76 of SMT-LIB Standard 2.6.
struct Sorter {
    local_symbol_table: HashMap<KRPKIdentifier, Vec<KRPKGroundSort>>,
}

impl Sorter {
    fn new() -> Self {
        Self {
            local_symbol_table: Default::default(),
        }
    }

    fn sort(
        &mut self,
        env: &KRPKEnvironment,
        term: &Sorted<KRPKTerm>,
    ) -> Result<Sorted<KRPKTerm>, AnalyzerError> {
        assert!(term.sort().is_none());
        assert_eq!(KRPKLogic::All, env.logic());
        match term.inner() {
            KRPKTerm::SpecConstant(spec_constant) => match spec_constant {
                KRPKSpecConstant::Hexadecimal(hex) => {
                    Ok(term.create_sorted(make_bv_sort(hex.bit_num())))
                }
                KRPKSpecConstant::Binary(bin) => {
                    Ok(term.create_sorted(make_bv_sort(bin.bit_num())))
                }
                _ => unimplemented!(),
            },
            KRPKTerm::Identifier(qid) => {
                let (id, expected) = match qid {
                    KRPKQualIdentifier::Simple(id) => (id, None),
                    KRPKQualIdentifier::Qualified(id, sort) => (id, Some(sort.clone())),
                };
                let local = self.local_symbol_table.get(id);
                if let Some(stack) = local {
                    let sort = stack.last().unwrap().clone();
                    Ok(term.create_sorted(sort))
                } else {
                    let func = env.lookup_function(id).map_err(|err| match err {
                        FunctionError::Undefined(id) => AnalyzerError::UndefinedSymbol(id),
                    })?;
                    let decl = match func {
                        crate::smtanalyze::KRPKFunction::Predefined(decl) => Either::Left(decl),
                        crate::smtanalyze::KRPKFunction::DeclaredConstant(decl) => {
                            Either::Left(decl)
                        }
                        crate::smtanalyze::KRPKFunction::CBFunction(decl) => Either::Right(decl),
                    };
                    let sort = {
                        let tmp = decl
                            .clone()
                            .map_either(|decl| decl.map_sort(&[]), |decl| decl.map_sort(&[]));
                        match tmp {
                            Either::Left(sort) => sort,
                            Either::Right(sort) => sort,
                        }
                    }
                    .ok_or({
                        let tmp = decl.map_either(
                            |decl| AnalyzerError::SignatureMismatch(decl, vec![]),
                            AnalyzerError::CBSignatureMismatch,
                        );
                        match tmp {
                            Either::Left(err) => err,
                            Either::Right(err) => err,
                        }
                    })?;
                    if let Some(expected) = expected {
                        // XXX: Support coercion?
                        if expected != sort {
                            return Err(AnalyzerError::SortMismatch {
                                expected,
                                actual: sort,
                            });
                        }
                    }
                    Ok(term.create_sorted(sort))
                }
            }
            KRPKTerm::Let(bindings, inner) => {
                let mut sorted_bindings = vec![];
                for (v, t) in bindings {
                    let sorted_t = self.sort(env, &t.clone())?;
                    let sort = sorted_t.sort().clone().unwrap();
                    sorted_bindings.push((v.clone(), sorted_t));
                    self.local_symbol_table
                        .entry(v.clone())
                        .or_default()
                        .push(sort);
                }
                let sorted_inner = self.sort(env, &inner.clone().map_inner(|item| *item))?;
                let sort = sorted_inner.sort().clone().unwrap();
                Ok(Sorted::with_sort(
                    KRPKTerm::Let(sorted_bindings, sorted_inner.map_inner(Box::new)),
                    sort,
                ))
            }
            KRPKTerm::Forall(sorted, inner) => {
                for (id, sort) in sorted {
                    self.local_symbol_table
                        .entry(id.clone())
                        .or_default()
                        .push(sort.clone());
                }
                let inner_sorted = self.sort(env, &inner.clone().map_inner(|item| *item))?;
                for (id, _) in sorted {
                    self.local_symbol_table.entry(id.clone()).or_default().pop();
                }
                let sort = inner_sorted.sort().clone().unwrap();
                if !sort.is_bool() {
                    return Err(AnalyzerError::SortMismatch {
                        expected: env.bool_sort(),
                        actual: sort,
                    });
                }
                Ok(Sorted::with_sort(
                    KRPKTerm::Forall(sorted.clone(), inner_sorted.map_inner(Box::new)),
                    sort,
                ))
            }
            KRPKTerm::Exists(sorted, inner) => {
                for (id, sort) in sorted {
                    self.local_symbol_table
                        .entry(id.clone())
                        .or_default()
                        .push(sort.clone());
                }
                let inner_sorted = self.sort(env, &inner.clone().map_inner(|item| *item))?;
                for (id, _) in sorted {
                    self.local_symbol_table.entry(id.clone()).or_default().pop();
                }
                let sort = inner_sorted.sort().clone().unwrap();
                if !sort.is_bool() {
                    return Err(AnalyzerError::SortMismatch {
                        expected: env.bool_sort(),
                        actual: sort,
                    });
                }
                Ok(Sorted::with_sort(
                    KRPKTerm::Exists(sorted.clone(), inner_sorted.map_inner(Box::new)),
                    sort,
                ))
            }
            KRPKTerm::Match(_, _) => unimplemented!(),
            KRPKTerm::Apply(func_id, args) => {
                let (simple_id, coercion_sort) = match func_id {
                    KRPKQualIdentifier::Simple(id) => (id, None),
                    KRPKQualIdentifier::Qualified(id, sort) => (id, Some(sort.clone())),
                };
                let func = env.lookup_function(simple_id).map_err(|err| match err {
                    FunctionError::Undefined(id) => AnalyzerError::UndefinedSymbol(id),
                })?;
                let mut sorted_args = Vec::with_capacity(args.len());
                let mut arg_and_coercion_sorts = Vec::with_capacity(args.len());
                for arg in args {
                    let sorted_arg = self.sort(env, &arg.clone())?;
                    let sort = sorted_arg.sort().clone().unwrap();
                    sorted_args.push(sorted_arg);
                    arg_and_coercion_sorts.push(sort);
                }
                if let Some(coercion_sort) = coercion_sort {
                    arg_and_coercion_sorts.push(coercion_sort);
                }
                let decl = match func {
                    KRPKFunction::Predefined(decl) => Either::Left(decl),
                    KRPKFunction::DeclaredConstant(decl) => Either::Left(decl),
                    KRPKFunction::CBFunction(decl) => Either::Right(decl),
                };
                let sort = {
                    let tmp = decl.clone().map_either(
                        |decl| decl.map_sort(&arg_and_coercion_sorts),
                        |decl| decl.map_sort(&arg_and_coercion_sorts),
                    );
                    match tmp {
                        Either::Left(sort) => sort,
                        Either::Right(sort) => sort,
                    }
                }
                .ok_or({
                    let tmp = decl.clone().map_either(
                        |decl| {
                            AnalyzerError::SignatureMismatch(
                                decl,
                                sorted_args
                                    .iter()
                                    .map(|st| st.sort().as_ref().unwrap().clone())
                                    .collect_vec(),
                            )
                        },
                        AnalyzerError::CBSignatureMismatch,
                    );
                    match tmp {
                        Either::Left(err) => err,
                        Either::Right(err) => err,
                    }
                })?;
                Ok(Sorted::with_sort(
                    KRPKTerm::Apply(func_id.clone(), sorted_args),
                    sort,
                ))
            }
        }
    }
}

fn make_bv_sort(bit_num: usize) -> KRPKGroundSort {
    KRPKGroundSort::new(
        KRPKIdentifier::numeral_indexed("BitVec", &[bit_num]),
        vec![],
    )
}

/// [`Analyzer`] interprets a [`SMTScript`] and constructs an [`KRPKEnvironment`] that relates syntax constructs to semantic objects.
/// In this process, it also performs high-level optimizations on the AST.
pub struct Analyzer {
    analyses: Vec<Box<dyn Fn(KRPKEnvironment) -> Result<KRPKEnvironment, AnalyzerError>>>,
}

impl Analyzer {
    /// Emulate a solver's behavior according to Figure 4.1 on page 52 of SMT-LIB Standard 2.6.
    /// `Sat` mode and `Unsat` mode are merged to [`EmulatedSolverMode::AfterCheck`] mode since we do not actually conduct checking.
    /// After th emulation, an KRPKEnvironment that interprets syntax constructs and semantic objects is constructed.
    pub(self) fn build_environment(script: &SMTScript) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut mode = EmulatedSolverMode::Start;
        let SMTScript(commands) = script;
        let mut logic = KRPKLogic::All;

        let mut env = KRPKEnvironment::with_logic(logic);

        let mut step = |mode: EmulatedSolverMode,
                        command: &Command|
         -> Result<EmulatedSolverMode, AnalyzerError> {
            match mode {
                EmulatedSolverMode::Start => {
                    match command {
                        Command::Echo(msg) => {
                            info!("echo: {}", msg);
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::Reset => {
                            info!("reset");
                            env.reset_assertions();
                            env.set_logic(KRPKLogic::All);
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::ResetAssertions => {
                            info!("reset-assertions");
                            env.reset_assertions();
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::GetInfo(info_flag) => {
                            match info_flag {
                                crate::hir::InfoFlag::Authors => {
                                    info!("get-info authors: (:authors Chuyang Chen)");
                                }
                                crate::hir::InfoFlag::ErrorBehavior => {
                                    info!(
                                        "get-info error-behavior: (:error-behavior immediate-exit)"
                                    );
                                }
                                crate::hir::InfoFlag::Name => {
                                    info!("get-info name: (:name \"krpk\")");
                                }
                                crate::hir::InfoFlag::Version => {
                                    info!("get-info version: (:version \"0.1.0\")");
                                }
                                _ => {
                                    warn!("get-info: {:?} not supported", info_flag);
                                }
                            }
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::GetOption(option) => {
                            let Keyword(option) = option;
                            match option.as_str() {
                                "diagnostic-output-channel" => {
                                    info!("get-option diagnostic-output-channel: stderr");
                                }
                                "global-declarations" => {
                                    info!("get-option global-declarations: true");
                                }
                                "print-success" => {
                                    info!("get-option print-success: true");
                                }
                                "produce-assertions" => {
                                    info!("get-option produce-assertions: true");
                                }
                                "produce-assignments" => {
                                    info!("get-option produce-assignments: false");
                                }
                                "produce-models" => {
                                    info!("get-option produce-models: true");
                                }
                                "produce-proofs" => {
                                    info!("get-option produce-proofs: false");
                                }
                                "produce-unsat-assumptions" => {
                                    info!("get-option produce-unsat-assumptions: false");
                                }
                                "produce-unsat-cores" => {
                                    info!("get-option produce-unsat-cores: false");
                                }
                                "regular-output-channel" => {
                                    info!("get-option regular-output-channel: stdout");
                                }
                                "verbosity" => {
                                    // TODO: Make this configurable
                                    info!("get-option verbosity: 0");
                                }
                                _ => {
                                    warn!("get-option: {:?} not supported", option);
                                }
                            }
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::SetInfo(_info) => {
                            warn!("set-info: not supported");
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::SetOption(option) => {
                            match option {
                                SMTOption::Verbosity(_) => {
                                    warn!("set-option verbosity: todo")
                                }
                                _ => {
                                    warn!("set-option: {:?} not supported", option);
                                }
                            }
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::SetArch(arch) => match arch {
                            Symbol::Simple(name) => {
                                match name.as_str() {
                                    "X86" => {
                                        let r = env.set_arch(KRPKArch::X86);
                                        if r.is_some() {
                                            return Err(AnalyzerError::MultipleSetArch);
                                        }
                                    }
                                    _ => unimplemented!("Only support X86 for now"),
                                }
                                Ok(EmulatedSolverMode::Start)
                            }
                            _ => Err(AnalyzerError::UnknownArch(format!("{:?}", arch))),
                        },
                        Command::SetLogic(logic) => match logic {
                            Symbol::Simple(name) => {
                                match name.as_str() {
                                    "ALL" => {
                                        env.set_logic(KRPKLogic::All);
                                    }
                                    "CORE" => {
                                        env.set_logic(KRPKLogic::Core);
                                    }
                                    _ => {
                                        warn!("set-logic: currently we fix the logic to be ALL or CORE");
                                        env.set_logic(KRPKLogic::All);
                                    }
                                };
                                Ok(EmulatedSolverMode::Assert)
                            }
                            Symbol::Quoted(_) => {
                                Err(AnalyzerError::UnknownLogic(format!("{:?}", logic)))
                            }
                        },
                        Command::Exit => {
                            info!("exit");
                            Ok(EmulatedSolverMode::Exit)
                        }
                        _ => Err(AnalyzerError::DisallowedCommand(
                            mode,
                            format!("{:?}", command),
                        )),
                    }
                }
                EmulatedSolverMode::Assert => {
                    match command {
                        Command::Echo(msg) => {
                            info!("echo: {}", msg);
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::ResetAssertions => {
                            info!("reset-assertions");
                            env.reset_assertions();
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::SetArch(arch) => match arch {
                            Symbol::Simple(name) => {
                                match name.as_str() {
                                    "X86" => {
                                        let r = env.set_arch(KRPKArch::X86);
                                        if r.is_some() {
                                            return Err(AnalyzerError::MultipleSetArch);
                                        }
                                    }
                                    _ => unimplemented!("Only support X86 for now"),
                                }
                                Ok(EmulatedSolverMode::Assert)
                            }
                            _ => Err(AnalyzerError::UnknownArch(format!("{:?}", arch))),
                        },
                        Command::GetInfo(info_flag) => {
                            match info_flag {
                                crate::hir::InfoFlag::Authors => {
                                    info!("get-info authors: (:authors Chuyang Chen)");
                                }
                                crate::hir::InfoFlag::ErrorBehavior => {
                                    info!(
                                        "get-info error-behavior: (:error-behavior immediate-exit)"
                                    );
                                }
                                crate::hir::InfoFlag::Name => {
                                    info!("get-info name: (:name \"krpk\")");
                                }
                                crate::hir::InfoFlag::Version => {
                                    info!("get-info version: (:version \"0.1.0\")");
                                }
                                _ => {
                                    warn!("get-info: {:?} not supported", info_flag);
                                }
                            }
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::GetOption(option) => {
                            let Keyword(option) = option;
                            match option.as_str() {
                                "diagnostic-output-channel" => {
                                    info!("get-option diagnostic-output-channel: stderr");
                                }
                                "global-declarations" => {
                                    info!("get-option global-declarations: true");
                                }
                                "print-success" => {
                                    info!("get-option print-success: true");
                                }
                                "produce-assertions" => {
                                    info!("get-option produce-assertions: true");
                                }
                                "produce-assignments" => {
                                    info!("get-option produce-assignments: false");
                                }
                                "produce-models" => {
                                    info!("get-option produce-models: true");
                                }
                                "produce-proofs" => {
                                    info!("get-option produce-proofs: false");
                                }
                                "produce-unsat-assumptions" => {
                                    info!("get-option produce-unsat-assumptions: false");
                                }
                                "produce-unsat-cores" => {
                                    info!("get-option produce-unsat-cores: false");
                                }
                                "regular-output-channel" => {
                                    info!("get-option regular-output-channel: stdout");
                                }
                                "verbosity" => {
                                    // TODO: Make this configurable
                                    info!("get-option verbosity: 0");
                                }
                                _ => {
                                    warn!("get-option: {:?} not supported", option);
                                }
                            }
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::SetInfo(_info) => {
                            warn!("set-info: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::SetOption(option) => {
                            match option {
                                SMTOption::Verbosity(_) => {
                                    warn!("set-option verbosity: todo")
                                }
                                _ => {
                                    warn!("set-option: {:?} not supported", option);
                                }
                            }
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::Pop(_) => {
                            warn!("pop: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::Push(_) => {
                            warn!("push: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::GetAssertions => {
                            // TODO: The current format doesn't conform to the standard.
                            info!(
                                "get-assertions: (\n{}\n)",
                                env.assertions()
                                    .iter()
                                    .map(|t| format!("  {:?}", t))
                                    .collect::<Vec<_>>()
                                    .join("\n")
                            );
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::Reset => {
                            info!("reset");
                            env.reset_assertions();
                            logic = KRPKLogic::All;
                            Ok(EmulatedSolverMode::Start)
                        }
                        Command::Assert(term) => {
                            let t = env.interpret_term(term);
                            env.push_assertion(t);
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareConst(symbol, sort) => {
                            env.declare_const(symbol, sort)
                                .map_err(|err| AnalyzerError::FunctionDeclarationError(err))?;
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DefineCType(symbol, sort) => {
                            env.define_ctype(symbol, sort)
                                .map_err(|err| AnalyzerError::CTypeDeclarationError(err))?;
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareCB(symbol, param_sorts, return_sort) => {
                            env.declare_cb(symbol, param_sorts, return_sort)
                                .map_err(|err| AnalyzerError::FunctionDeclarationError(err))?;
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareDatatype(_, _) => {
                            warn!("declare-datatype: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareDatatypes(_, _) => {
                            warn!("declare-datatypes: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareFun(_, _, _) => {
                            warn!("declare-fun: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DeclareSort(_, _) => {
                            warn!("declare-sort: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DefineFun(_) => {
                            warn!("define-fun: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DefineFunRec(_) => {
                            warn!("define-fun-rec: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DefineFunsRec(_, _) => {
                            warn!("define-funs-rec: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::DefineSort(_, _, _) => {
                            warn!("define-sort: not supported");
                            Ok(EmulatedSolverMode::Assert)
                        }
                        Command::CheckSat => {
                            info!("check-sat: dummy check");
                            Ok(EmulatedSolverMode::AfterCheck)
                        }
                        Command::CheckSatAssuming(_) => {
                            warn!("check-sat-assuming: not supported");
                            Ok(EmulatedSolverMode::AfterCheck)
                        }
                        Command::Exit => {
                            info!("exit");
                            Ok(EmulatedSolverMode::Exit)
                        }
                        Command::Alloc(addr, size, value) => {
                            if env.arch().is_none() {
                                return Err(AnalyzerError::ArchUnset);
                            }
                            assert_eq!(KRPKArch::X86, env.arch().unwrap());
                            let (addr_bits, addr_value) = env.interpret_hex(addr);
                            assert!(addr_bits <= 64);
                            let addr_value = addr_value.unwrap();

                            let size = env.interpret_numeral(size);
                            match value {
                                MemoryCell::Term(value) => {
                                    let value = env.interpret_term(value);

                                    env.alloc(&addr_value, size, value).map_err(
                                        |err| match err {
                                            AllocError::ReAlloc(addr) => {
                                                AnalyzerError::AllocOverlap(addr, size, addr_value)
                                            }
                                        },
                                    )?;
                                }
                                MemoryCell::HexBytes(hex_bytes) => {
                                    env.alloc_seg(&addr_value, size, &hex_bytes.0).map_err(
                                        |err| match err {
                                            AllocError::ReAlloc(addr) => {
                                                AnalyzerError::AllocOverlap(addr, size, addr_value)
                                            }
                                        },
                                    )?;
                                }
                            }
                            Ok(EmulatedSolverMode::Assert)
                        }
                        _ => Err(AnalyzerError::DisallowedCommand(
                            mode,
                            format!("{:?}", command),
                        )),
                    }
                }
                EmulatedSolverMode::AfterCheck => match command {
                    Command::Echo(msg) => {
                        info!("echo: {}", msg);
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::CheckSat => {
                        info!("check-sat: dummy check");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::CheckSatAssuming(_) => {
                        warn!("check-sat-assuming: not supported");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetAssertions => {
                        info!(
                            "get-assertions: (\n{}\n)",
                            env.assertions()
                                .iter()
                                .map(|t| format!("  {:?}", t))
                                .collect::<Vec<_>>()
                                .join("\n")
                        );
                        Ok(EmulatedSolverMode::Assert)
                    }
                    Command::GetAssignment => {
                        warn!("get-assignment: not supported");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetModel => {
                        info!("get-model: dummy get");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetValue(_) => {
                        info!("get-value: dummy get");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetProof => {
                        warn!("get-proof: not supported");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetUnsatCore => {
                        warn!("get-unsat-core: not supported");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::GetUnsatAssumptions => {
                        warn!("get-unsat-assumptions: not supported");
                        Ok(EmulatedSolverMode::AfterCheck)
                    }
                    Command::Reset => {
                        info!("reset");
                        env.reset_assertions();
                        logic = KRPKLogic::All;
                        Ok(EmulatedSolverMode::Start)
                    }
                    Command::Exit => {
                        info!("exit");
                        Ok(EmulatedSolverMode::Exit)
                    }
                    _ => Err(AnalyzerError::DisallowedCommand(
                        mode,
                        format!("{:?}", command),
                    )),
                },
                EmulatedSolverMode::Exit => Err(AnalyzerError::DisallowedCommand(
                    mode,
                    format!("{:?}", command),
                )),
            }
        };

        for command in commands {
            mode = step(mode, command)?;
            if let EmulatedSolverMode::Exit = mode {
                break;
            }
        }
        Ok(env)
    }

    /// Reduce `(concat bv_const1 bv_const2)` to a compile-time computed `BitVec` constant.
    pub(self) fn constant_reduction_analysis(
        env: KRPKEnvironment,
    ) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut env = env;
        let assertions = env.reset_assertions();
        for assertion in assertions {
            let (_c, new_one) = __reduce_constant(&env, &assertion);
            env.push_assertion(new_one);
        }

        let memory = env.reset_memory();
        for (addr, (size, value)) in memory {
            let Either::Left(value) = value else {
                env.alloc_seg(&addr, size, &value.unwrap_right());
                continue;
            };
            let (_c, new_value) = __reduce_constant(&env, &value);
            env.alloc(&addr, size, new_value).unwrap();
        }
        Ok(env)
    }

    /// Compute the index range of an array. It assumes all `select` happens on a (maybe-got-by-reduction) bv constant.
    /// Then, the max bv constant is the upper bound of the indices.
    pub(self) fn array_index_analysis(
        env: KRPKEnvironment,
    ) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut env = env;
        fn visit(env: &mut KRPKEnvironment, term: &Sorted<KRPKTerm>) {
            match term.inner() {
                KRPKTerm::SpecConstant(_) => {}
                KRPKTerm::Identifier(_) => {}
                KRPKTerm::Let(bindings, inner) => {
                    for (_, t) in bindings {
                        visit(env, t);
                    }
                    visit(env, &inner.clone().map_inner(|t| *t));
                }
                KRPKTerm::Forall(_, inner) => {
                    visit(env, &inner.clone().map_inner(|t| *t));
                }
                KRPKTerm::Exists(_, inner) => {
                    visit(env, &inner.clone().map_inner(|t| *t));
                }
                KRPKTerm::Match(_, match_cases) => {
                    for case in match_cases {
                        visit(env, &case.inner().body);
                    }
                }
                KRPKTerm::Apply(func_id, args) => {
                    let func_id = match func_id {
                        KRPKQualIdentifier::Simple(id) => id,
                        KRPKQualIdentifier::Qualified(id, _) => id,
                    };
                    let func = env.lookup_function(func_id).unwrap();

                    #[rustfmt::skip] // `rustfmt` will wrongly delete the label, so temporarily disable it for the match.
                    match func {
                        KRPKFunction::Predefined(decl) => {
                            let KRPKFunctionDeclaration { id, .. } = decl;
                            match &id {
                                KRPKIdentifier::Symbol(name) => 'select_branch: {
                                    match name.as_str() {
                                        "ensure_index" => {
                                            let array_id = args.get(0).unwrap();
                                            let max_idx = args.get(1).unwrap();
                                            let KRPKTerm::Identifier(array_id) = array_id.inner() else {
                                                break 'select_branch;
                                            };
                                            let array_id = match array_id {
                                                KRPKQualIdentifier::Qualified(id, _sort) => id,
                                                KRPKQualIdentifier::Simple(id) => id,
                                            };
                                            assert!(max_idx.sort().clone().unwrap().is_bit_vec());
                                            let KRPKTerm::SpecConstant(spec_const) = max_idx.inner() else {
                                                unimplemented!(
                                                    "Only support ensuring constant index."
                                                )
                                            };
                                            let idx = match spec_const {
                                                KRPKSpecConstant::Hexadecimal(hex) => hex.value(),
                                                KRPKSpecConstant::Binary(bin) => bin.value(),
                                                _ => unreachable!()
                                            }
                                            .unwrap();
                                            env.update_array_index_bound(&array_id, idx);
                                        }
                                        "select" | "store" => {
                                            let array_id = args.get(0).unwrap();
                                            let index = args.get(1).unwrap();
                                            let KRPKTerm::Identifier(array_id) = array_id.inner() else {
                                                break 'select_branch;
                                            };
                                            let array_id = match array_id {
                                                KRPKQualIdentifier::Qualified(id, _sort) => id,
                                                KRPKQualIdentifier::Simple(id) => id,
                                            };
                                            assert!(index.sort().clone().unwrap().is_bit_vec());
                                            let KRPKTerm::SpecConstant(spec_const) = index.inner() else {
                                                break 'select_branch;
                                            };
                                            let idx = match spec_const {
                                                KRPKSpecConstant::Hexadecimal(hex) => hex.value(),
                                                KRPKSpecConstant::Binary(bin) => bin.value(),
                                                _ => unreachable!(),
                                            }
                                            .unwrap();
                                            env.update_array_index_bound(&array_id, idx);
                                            return;
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    };
                    for arg in args {
                        visit(env, arg);
                    }
                }
            }
        }
        let assertions = env.reset_assertions();
        for assertion in assertions {
            visit(&mut env, &assertion);
            env.push_assertion(assertion);
        }

        let memory = env.reset_memory();
        for (addr, (size, value)) in memory {
            let Either::Left(value) = value else {
                env.alloc_seg(&addr, size, &value.unwrap_right());
                continue;
            };
            visit(&mut env, &value);
            env.alloc(&addr, size, value).unwrap();
        }
        Ok(env)
    }

    /// Designate a sort for every term.
    pub(self) fn sort_analysis(env: KRPKEnvironment) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut env = env;
        let mut sorter = Sorter::new();
        let unsorted = env.reset_assertions();
        for t in unsorted {
            let sorted_t = sorter.sort(&env, &t)?;
            env.push_assertion(sorted_t);
        }

        fn max_addr_less_than(memory: &BTreeMap<u64, usize>, addr: &u64) -> Option<(u64, usize)> {
            memory
                .iter()
                .rev()
                .find(|(a, _)| *a < addr)
                .map(|(addr, size)| (*addr, *size))
        }

        fn min_addr_greater_than(
            memory: &BTreeMap<u64, usize>,
            addr: &u64,
        ) -> Option<(u64, usize)> {
            memory
                .iter()
                .find(|(a, _)| *a > addr)
                .map(|(addr, size)| (*addr, *size))
        }

        let unsorted_memory = env.reset_memory();
        let addr_and_size = unsorted_memory
            .iter()
            .map(|(addr, (size, _))| (*addr, *size))
            .collect::<BTreeMap<_, _>>();
        for (addr, (alloc_size, cell)) in unsorted_memory {
            let Either::Left(value) = cell else {
                let tmp = cell.as_ref().unwrap_right().len();
                if 2 * alloc_size != tmp {
                    return Err(AnalyzerError::AllocSizeMismatch(
                        (alloc_size * 8) as u64,
                        (tmp * 4) as u64,
                    ));
                }
                env.alloc_seg(&addr, alloc_size, &cell.unwrap_right());
                continue;
            };
            let sorted_value = sorter.sort(&env, &value)?;

            let data_size = env.size_of(sorted_value.sort().as_ref().unwrap());
            match data_size {
                None => {
                    return Err(AnalyzerError::AllocUnsized(
                        addr,
                        sorted_value.sort().clone().unwrap(),
                    ));
                }
                Some(data_size) => {
                    if data_size > alloc_size {
                        return Err(AnalyzerError::AllocOverflow(
                            addr,
                            alloc_size,
                            sorted_value.sort().clone().unwrap(),
                        ));
                    }
                    if let Some((lower_bound, lb_size)) = max_addr_less_than(&addr_and_size, &addr)
                    {
                        if lower_bound + (lb_size as u64) > addr {
                            return Err(AnalyzerError::AllocOverlap(lower_bound, lb_size, addr));
                        }
                    }
                    if let Some((upper_bound, _ub_size)) =
                        min_addr_greater_than(&addr_and_size, &addr)
                    {
                        if addr + (alloc_size as u64) > upper_bound {
                            return Err(AnalyzerError::AllocOverlap(addr, alloc_size, upper_bound));
                        }
                    }
                }
            }
            env.alloc(&addr, alloc_size, sorted_value).unwrap();
        }

        Ok(env)
    }

    /// Create an analyzer with default analyses/optimizations including sort analysis, constant reduction optimization,
    /// and array index analysis (which infers upper bounds of array indices).
    pub fn new() -> Self {
        Self {
            analyses: vec![
                Box::new(Self::sort_analysis),
                Box::new(Self::constant_reduction_analysis),
                Box::new(Self::array_index_analysis),
                Box::new(Self::address_range_analysis),
            ],
        }
    }

    /// Constructs semantic objects from the AST and performs in sequence the analyses/optimizations specified in `self.analyses`.
    pub fn analyze(&mut self, script: &SMTScript) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut env = Self::build_environment(script)?;
        for analysis in self.analyses.iter() {
            env = analysis(env)?;
        }
        Ok(env)
    }

    fn address_range_analysis(env: KRPKEnvironment) -> Result<KRPKEnvironment, AnalyzerError> {
        let mut env = env;
        let assertions = env.reset_assertions();

        fn get_implicit_max_and_min(
            env: &KRPKEnvironment,
            term: &Sorted<KRPKTerm>,
        ) -> (Option<(u64, usize)>, Option<(u64, usize)>) {
            match term.inner() {
                KRPKTerm::SpecConstant(_) => (None, None),
                KRPKTerm::Identifier(_) => (None, None),
                KRPKTerm::Let(bindings, inner) => {
                    let mut max = None;
                    let mut min = None;
                    for (_, t) in bindings {
                        let (t_max, t_min) = get_implicit_max_and_min(env, t);
                        if let Some((t_max_addr, t_max_size)) = t_max {
                            if let Some((max_addr, max_size)) = max {
                                if t_max_addr + (t_max_size as u64) > max_addr + (max_size as u64) {
                                    max = Some((t_max_addr, t_max_size));
                                }
                            } else {
                                max = Some((t_max_addr, t_max_size));
                            }
                        }
                        if let Some(t_min_addr) = t_min {
                            if let Some(min_addr) = min {
                                if t_min_addr < min_addr {
                                    min = Some(t_min_addr);
                                }
                            } else {
                                min = Some(t_min_addr);
                            }
                        }
                    }
                    let (inner_max, inner_min) =
                        get_implicit_max_and_min(env, &inner.clone().map_inner(|t| *t));
                    if let Some((inner_max_addr, inner_max_size)) = inner_max {
                        if let Some((max_addr, max_size)) = max {
                            if inner_max_addr + (inner_max_size as u64)
                                > max_addr + (max_size as u64)
                            {
                                max = Some((inner_max_addr, inner_max_size));
                            }
                        } else {
                            max = Some((inner_max_addr, inner_max_size));
                        }
                    }
                    if let Some(inner_min_addr) = inner_min {
                        if let Some(min_addr) = min {
                            if inner_min_addr < min_addr {
                                min = Some(inner_min_addr);
                            }
                        } else {
                            min = Some(inner_min_addr);
                        }
                    }
                    (max, min)
                }
                KRPKTerm::Forall(_, inner) | KRPKTerm::Exists(_, inner) => {
                    get_implicit_max_and_min(env, &inner.clone().map_inner(|t| *t))
                }
                KRPKTerm::Match(expr, cases) => {
                    let (expr_max, expr_min) =
                        get_implicit_max_and_min(env, &expr.clone().map_inner(|t| *t));
                    let mut max = expr_max;
                    let mut min = expr_min;
                    for case in cases {
                        let (case_max, case_min) =
                            get_implicit_max_and_min(env, &case.inner().body);
                        if let Some((case_max_addr, case_max_size)) = case_max {
                            if let Some((max_addr, max_size)) = max {
                                if case_max_addr + (case_max_size as u64)
                                    > max_addr + (max_size as u64)
                                {
                                    max = Some((case_max_addr, case_max_size));
                                }
                            } else {
                                max = Some((case_max_addr, case_max_size));
                            }
                        }
                        if let Some(case_min_addr) = case_min {
                            if let Some(min_addr) = min {
                                if case_min_addr < min_addr {
                                    min = Some(case_min_addr);
                                }
                            } else {
                                min = Some(case_min_addr);
                            }
                        }
                    }
                    (max, min)
                }
                KRPKTerm::Apply(func_id, args) => {
                    let mut max = None;
                    let mut min = None;
                    for arg in args {
                        let (arg_max, arg_min) = get_implicit_max_and_min(env, arg);
                        if let Some((arg_max_addr, arg_max_size)) = arg_max {
                            if let Some((max_addr, max_size)) = max {
                                if arg_max_addr + (arg_max_size as u64)
                                    > max_addr + (max_size as u64)
                                {
                                    max = Some((arg_max_addr, arg_max_size));
                                }
                            } else {
                                max = Some((arg_max_addr, arg_max_size));
                            }
                        }
                        if let Some(arg_min_addr) = arg_min {
                            if let Some(min_addr) = min {
                                if arg_min_addr < min_addr {
                                    min = Some(arg_min_addr);
                                }
                            } else {
                                min = Some(arg_min_addr);
                            }
                        }
                    }

                    let func = env
                        .lookup_function({
                            match func_id {
                                KRPKQualIdentifier::Qualified(id, _) => id,
                                KRPKQualIdentifier::Simple(id) => id,
                            }
                        })
                        .unwrap();
                    if let KRPKFunction::CBFunction(cb_func) = func {
                        let name = {
                            let tmp = cb_func.id;
                            let KRPKIdentifier::Symbol(name) = tmp else {
                                unreachable!()
                            };
                            name
                        };
                        let visited = match name.as_str() {
                            "memchr" | "memset" => match (args[0].inner(), args[2].inner()) {
                                (
                                    KRPKTerm::SpecConstant(KRPKSpecConstant::Hexadecimal(addr_hex)),
                                    KRPKTerm::SpecConstant(KRPKSpecConstant::Hexadecimal(sz_hex)),
                                ) => {
                                    let addr = addr_hex.value().unwrap();
                                    let size = sz_hex.value().unwrap();
                                    vec![(addr, size)]
                                }
                                (KRPKTerm::SpecConstant(..), KRPKTerm::SpecConstant(..)) => {
                                    unimplemented!()
                                }
                                _ => Default::default(),
                            },
                            "memcmp" | "memcpy" | "memmove" => {
                                match (args[0].inner(), args[1].inner(), args[2].inner()) {
                                    (
                                        KRPKTerm::SpecConstant(KRPKSpecConstant::Hexadecimal(
                                            addr1_hex,
                                        )),
                                        KRPKTerm::SpecConstant(KRPKSpecConstant::Hexadecimal(
                                            addr2_hex,
                                        )),
                                        KRPKTerm::SpecConstant(KRPKSpecConstant::Hexadecimal(
                                            sz_hex,
                                        )),
                                    ) => {
                                        let addr1 = addr1_hex.value().unwrap();
                                        let addr2 = addr2_hex.value().unwrap();
                                        let size = sz_hex.value().unwrap();
                                        vec![(addr1, size), (addr2, size)]
                                    }
                                    (
                                        KRPKTerm::SpecConstant(..),
                                        KRPKTerm::SpecConstant(..),
                                        KRPKTerm::SpecConstant(..),
                                    ) => unimplemented!(),
                                    _ => Default::default(),
                                }
                            }
                            _ => Default::default(),
                        };
                        for (addr, sz) in visited {
                            if let Some((max_addr, max_size)) = max {
                                if addr + sz > max_addr + (max_size as u64) {
                                    max = Some((addr, sz as usize));
                                }
                            } else {
                                max = Some((addr, sz as usize));
                            }
                            if let Some((min_addr, _)) = min {
                                if addr < min_addr {
                                    min = Some((addr, sz as usize));
                                }
                            } else {
                                min = Some((addr, sz as usize));
                            }
                        }
                        (max, min)
                    } else {
                        (max, min)
                    }
                }
            }
        }

        for assertion in assertions {
            let (max, min) = get_implicit_max_and_min(&env, &assertion);
            if let Some((addr, sz)) = max {
                env.reserve_addr(&addr, sz);
            }
            if let Some((addr, sz)) = min {
                env.reserve_addr(&addr, sz);
            }
            env.push_assertion(assertion);
        }
        Ok(env)
    }
}

fn __reduce_constant(env: &KRPKEnvironment, term: &Sorted<KRPKTerm>) -> (bool, Sorted<KRPKTerm>) {
    match term.inner() {
        KRPKTerm::SpecConstant(spec_constant) => match spec_constant {
            KRPKSpecConstant::Hexadecimal(_) => (true, term.clone()),
            KRPKSpecConstant::Binary(_) => (true, term.clone()),
            _ => (false, term.clone()),
        },
        KRPKTerm::Identifier(_) => (false, term.clone()),
        KRPKTerm::Let(bindings, inner) => {
            let mut new_bindings = Vec::with_capacity(bindings.len());
            for (v, t) in bindings {
                let (_c, t) = __reduce_constant(env, t);
                new_bindings.push((v.clone(), t));
            }
            let (_c, inner) = __reduce_constant(env, &inner.clone().map_inner(|t| *t));
            (
                false,
                Sorted::with_sort(
                    KRPKTerm::Let(new_bindings, inner.map_inner(Box::new)),
                    term.sort().clone().unwrap(),
                ),
            )
        }
        KRPKTerm::Forall(sorted, inner) => {
            let (_c, inner) = __reduce_constant(env, &inner.clone().map_inner(|t| *t));
            (
                false,
                Sorted::with_sort(
                    KRPKTerm::Forall(sorted.clone(), inner.map_inner(Box::new)),
                    term.sort().clone().unwrap(),
                ),
            )
        }
        KRPKTerm::Exists(sorted, inner) => {
            let (_c, inner) = __reduce_constant(env, &inner.clone().map_inner(|t| *t));
            (
                false,
                Sorted::with_sort(
                    KRPKTerm::Exists(sorted.clone(), inner.map_inner(Box::new)),
                    term.sort().clone().unwrap(),
                ),
            )
        }
        KRPKTerm::Match(inner, match_cases) => {
            let (_c, inner) = __reduce_constant(env, &inner.clone().map_inner(|t| *t));
            let mut new_match_cases = Vec::with_capacity(match_cases.len());
            for case in match_cases {
                let sort = case.sort().clone().unwrap();
                let KRPKMatchCase { pattern, body } = case.inner();
                let (_c, body) = __reduce_constant(env, body);
                new_match_cases.push(Sorted::with_sort(
                    KRPKMatchCase {
                        pattern: pattern.clone(),
                        body,
                    },
                    sort,
                ));
            }
            (
                false,
                Sorted::with_sort(
                    KRPKTerm::Match(inner.map_inner(Box::new), new_match_cases),
                    term.sort().clone().unwrap(),
                ),
            )
        }
        KRPKTerm::Apply(original_func_id, args) => {
            let mut new_args = Vec::with_capacity(args.len());
            let mut all_bv_constants = true;
            for arg in args {
                let (c, arg) = __reduce_constant(env, arg);
                new_args.push(arg);
                all_bv_constants = all_bv_constants && c;
            }
            let simple_id = match original_func_id {
                KRPKQualIdentifier::Qualified(id, _) => id,
                KRPKQualIdentifier::Simple(id) => id,
            };
            let func = env.lookup_function(simple_id).unwrap();
            let KRPKFunction::Predefined(decl) = func else {
                return (
                    false,
                    Sorted::with_sort(
                        KRPKTerm::Apply(original_func_id.clone(), new_args),
                        term.sort().clone().unwrap(),
                    ),
                );
            };
            let KRPKFunctionDeclaration { id: func_id, .. } = decl;
            let name = match func_id {
                KRPKIdentifier::Symbol(name) => name,
                KRPKIdentifier::Indexed(name, _) => name,
            };
            match name.as_str() {
                "concat" => {
                    assert_eq!(2, args.len());
                    if !all_bv_constants {
                        (
                            false,
                            Sorted::with_sort(
                                KRPKTerm::Apply(original_func_id.clone(), new_args),
                                term.sort().clone().unwrap(),
                            ),
                        )
                    } else {
                        let [arg0, arg1] = new_args.as_slice() else {
                            unreachable!()
                        };
                        let KRPKTerm::SpecConstant(arg0) = arg0.inner() else {
                            unreachable!()
                        };
                        let KRPKTerm::SpecConstant(arg1) = arg1.inner() else {
                            unreachable!()
                        };
                        let new_constant = match (arg0, arg1) {
                            (
                                KRPKSpecConstant::Hexadecimal(first),
                                KRPKSpecConstant::Hexadecimal(second),
                            ) => KRPKSpecConstant::Hexadecimal(first.concat(second)),
                            (KRPKSpecConstant::Binary(first), KRPKSpecConstant::Binary(second)) => {
                                KRPKSpecConstant::Binary(first.concat(second))
                            }
                            (
                                KRPKSpecConstant::Hexadecimal(first),
                                KRPKSpecConstant::Binary(second),
                            ) => KRPKSpecConstant::Binary(Binary::concat(
                                &first.clone().into(),
                                second,
                            )),
                            (
                                KRPKSpecConstant::Binary(first),
                                KRPKSpecConstant::Hexadecimal(second),
                            ) => KRPKSpecConstant::Binary(first.concat(&second.clone().into())),
                            _ => unreachable!(),
                        };
                        (
                            true,
                            Sorted::with_sort(
                                KRPKTerm::SpecConstant(new_constant),
                                term.sort().clone().unwrap(),
                            ),
                        )
                    }
                }
                "extract" => {
                    assert_eq!(1, args.len());
                    if !all_bv_constants {
                        (
                            false,
                            Sorted::with_sort(
                                KRPKTerm::Apply(original_func_id.clone(), new_args),
                                term.sort().clone().unwrap(),
                            ),
                        )
                    } else {
                        let [arg] = new_args.as_slice() else {
                            unreachable!()
                        };
                        let KRPKTerm::SpecConstant(arg) = arg.inner() else {
                            unreachable!()
                        };
                        let KRPKIdentifier::Indexed(_, indices) = simple_id else {
                            unreachable!()
                        };
                        let [KRPKIndex::Numeral(to), KRPKIndex::Numeral(from)] = indices.as_slice()
                        else {
                            unreachable!()
                        };
                        assert!(0 == (*to + 1) % 8);
                        assert!(0 == *from % 8);
                        let from_byte = *from / 8;
                        let to_byte = (*to + 1) / 8;
                        let new_constant = match arg {
                            KRPKSpecConstant::Hexadecimal(hex) => {
                                let bytes = &hex.bytes;
                                let new_byte_num = to_byte - from_byte;
                                let mut new_bytes = vec![0; new_byte_num as usize + 1];
                                for i in 0..new_byte_num {
                                    new_bytes[i as usize] = bytes[(from_byte + i) as usize];
                                }
                                KRPKSpecConstant::Hexadecimal(Hexadecimal {
                                    bytes: new_bytes,
                                    digit_num: new_byte_num * 2,
                                })
                            }
                            KRPKSpecConstant::Binary(_) => unimplemented!(),
                            _ => unreachable!(),
                        };
                        (
                            true,
                            Sorted::with_sort(
                                KRPKTerm::SpecConstant(new_constant),
                                term.sort().clone().unwrap(),
                            ),
                        )
                    }
                }
                _ => (
                    false,
                    Sorted::with_sort(
                        KRPKTerm::Apply(original_func_id.clone(), new_args),
                        term.sort().clone().unwrap(),
                    ),
                ),
            }
        }
    }
}

#[cfg(test)]
mod test {
    // TODO: Check and/or/xor/implies/distinct/= with multiple arguments?

    use itertools::Itertools;
    use trim_margin::MarginTrimmable;

    use super::*;
    use crate::smtanalyze::SortError;
    use crate::smtparser::parse_str;

    #[test]
    fn test_build_environment() {
        let script = parse_str(
            &r#"
            |(set-logic CORE)
            |(assert true)
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        assert_eq!(KRPKLogic::Core, env.logic());
        assert_eq!(1, env.assertions().len());

        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 32))
            |(assert true)
            |(assert (= x #x00000001))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        assert_eq!(KRPKLogic::All, env.logic());
        assert_eq!(2, env.assertions().len());

        let script = parse_str(
            &r#"
            |(set-logic CORE)
            |(declare-const x (_ BitVec 32))
            |(assert true)
            |(assert (= x #x00000001))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let err = Analyzer::build_environment(&script).err().unwrap();
        let AnalyzerError::FunctionDeclarationError(err) = err else {
            panic!("err is {:?}", err)
        };
        let FunctionDeclarationError::SortError(err) = err else {
            panic!("err is {:?}", err)
        };
        let SortError::Undefined(id) = err else {
            panic!("err is {:?}", err)
        };
        assert_eq!("(_ BitVec 32)", id.to_string().as_str());

        let script = parse_str(
            &r#"
            |(set-arch X86)
            |(set-logic CORE)
            |(alloc #x00000000 1 true)
            |(assert true)
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        assert_eq!(KRPKArch::X86, env.arch().unwrap());
        assert_eq!(1, env.memory_allocs().collect_vec().len());
    }

    fn to_sort_tree(term: &Sorted<KRPKTerm>) -> String {
        let mut result = term
            .sort()
            .as_ref()
            .map(|s| format!("({}", s))
            .unwrap_or("null".to_string());
        match term.inner() {
            KRPKTerm::SpecConstant(_) => {}
            KRPKTerm::Identifier(_) => {}
            KRPKTerm::Let(bindings, inner) => {
                result.push_str(" (");
                for (_id, st) in bindings {
                    result.push_str(" ");
                    result.push_str(&to_sort_tree(st));
                }
                result.push_str(") ");
                result.push_str(&to_sort_tree(&inner.clone().map_inner(|t| *t)));
            }
            KRPKTerm::Forall(_sorted, inner) => {
                result.push_str(" ");
                result.push_str(&to_sort_tree(&inner.clone().map_inner(|t| *t)));
            }
            KRPKTerm::Exists(_sorted, inner) => {
                result.push_str(" ");
                result.push_str(&to_sort_tree(&inner.clone().map_inner(|t| *t)));
            }
            KRPKTerm::Match(t, match_cases) => {
                result.push_str(" ");
                result.push_str(&to_sort_tree(&t.clone().map_inner(|t| *t)));
                result.push_str(" (");
                let mut first = true;
                for case in match_cases {
                    if !first {
                        result.push_str(" ");
                    }
                    first = false;
                    result.push_str(&to_sort_tree(&case.inner().body));
                }
                result.push_str(")");
            }
            KRPKTerm::Apply(_func, args) => {
                result.push_str(" (");
                let mut first = true;
                for arg in args {
                    if !first {
                        result.push_str(" ");
                    }
                    first = false;
                    result.push_str(&to_sort_tree(arg));
                }
                result.push_str(")")
            }
        }
        result.push_str(")");
        return result;
    }

    #[test]
    fn test_sorting() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 32))
            |(assert (= 
            |    x 
            |    (concat 
            |        #x0001 
            |        (select ((as const (Array (_ BitVec 8) (_ BitVec 16))) #x0002) #x01)
            |    )
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        let env = Analyzer::sort_analysis(env).unwrap();
        let [assertion] = env.assertions() else {
            panic!("assertions are {:?}", env.assertions())
        };
        let result = to_sort_tree(assertion);
        assert_eq!("(Bool (((BitVec 32)) ((BitVec 32) (((BitVec 16)) ((BitVec 16) (((Array (BitVec 8) (BitVec 16)) (((BitVec 16)))) ((BitVec 8))))))))",
                   result.as_str());

        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(declare-const x (_ BitVec 32))
            |(alloc #x00000000 1 (= 
            |    x 
            |    (concat 
            |        #x0001 
            |        (select ((as const (Array (_ BitVec 8) (_ BitVec 16))) #x0002) #x01)
            |    )
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        let env = Analyzer::sort_analysis(env).unwrap();
        let (size, value) = env.get_alloc(0x0u64).unwrap();
        let Either::Left(value) = value else {
            panic!("value is {:?}", value)
        };
        assert_eq!(1, size);
        let result = to_sort_tree(value);
        assert_eq!("(Bool (((BitVec 32)) ((BitVec 32) (((BitVec 16)) ((BitVec 16) (((Array (BitVec 8) (BitVec 16)) (((BitVec 16)))) ((BitVec 8))))))))",
                   result.as_str());
    }

    #[test]
    fn test_constant() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 32))
            |(assert (= 
            |    x 
            |    (concat 
            |        #x01 
            |        (concat
            |           (concat #x02 #x03)
            |           #x04
            |        )
            |    )
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        let env =
            Analyzer::constant_reduction_analysis(Analyzer::sort_analysis(env).unwrap()).unwrap();
        let [assertion] = env.assertions() else {
            panic!("assertions are {:?}", env.assertions())
        };
        let represent = format!("{:?}", assertion);
        assert_eq!(
            r#"Apply(Simple(Symbol("=")), [Identifier(Simple(Symbol("x"))) : "#.to_owned()
                + r#"Some(KRPKGroundSort { id: Indexed("BitVec", [Numeral(32)]), args: [] }), SpecConstant(Hexadecimal(Hexadecimal"#
                + r#" { digit_num: 8, bytes: [4, 3, 2, 1] })) : Some(KRPKGroundSort { id: Indexed("BitVec", [Numeral(32)]), args: [] })]) :"#
                + r#" Some(KRPKGroundSort { id: Symbol("Bool"), args: [] })"#,
            represent
        );

        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 32))
            |(set-arch X86)
            |(alloc #x00000000 1 (= 
            |    x 
            |    (concat 
            |        #x01 
            |        (concat
            |           (concat #x02 #x03)
            |           #x04
            |        )
            |    )
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let env = Analyzer::build_environment(&script).unwrap();
        let env =
            Analyzer::constant_reduction_analysis(Analyzer::sort_analysis(env).unwrap()).unwrap();
        let (_size, value) = env.get_alloc(0x0u64).unwrap();
        let represent = format!("{:?}", value);
        assert_eq!(
            r#"Left(Apply(Simple(Symbol("=")), [Identifier(Simple(Symbol("x"))) : "#.to_owned()
                + r#"Some(KRPKGroundSort { id: Indexed("BitVec", [Numeral(32)]), args: [] }), SpecConstant(Hexadecimal(Hexadecimal"#
                + r#" { digit_num: 8, bytes: [4, 3, 2, 1] })) : Some(KRPKGroundSort { id: Indexed("BitVec", [Numeral(32)]), args: [] })]) :"#
                + r#" Some(KRPKGroundSort { id: Symbol("Bool"), args: [] }))"#,
            represent
        );
    }

    #[test]
    fn test_array() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (Array (_ BitVec 32) (_ BitVec 8)))
            |(assert (= 
            |    #x01
            |    (select x (concat 
            |        #x01 
            |        (concat
            |           (concat #x02 #x03)
            |           #x04
            |        )
            |    ))
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).unwrap();
        let id = KRPKIdentifier::Symbol("x".to_string());
        let index_bound = analyzed.get_array_index_bound(&id).unwrap();
        assert_eq!(0x01020304, index_bound);

        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(declare-const x (Array (_ BitVec 32) (_ BitVec 8)))
            |(alloc #x00000000 1 (= 
            |    #x01
            |    (select x (concat 
            |        #x01 
            |        (concat
            |           (concat #x02 #x03)
            |           #x04
            |        )
            |    ))
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).unwrap();
        let id = KRPKIdentifier::Symbol("x".to_string());
        let index_bound = analyzed.get_array_index_bound(&id).unwrap();
        assert_eq!(0x01020304, index_bound);
    }

    #[test]
    fn test_cb() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 32))
            |(define-ctype int (_ BitVec 32))
            |(declare-cb abs (int) int)
            |(assert (=
            |    #x00000001
            |    (abs x)
            |))
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).unwrap();

        let [assertion] = analyzed.assertions() else {
            panic!("assertions are {:?}", analyzed.assertions())
        };
        let sort_tree = to_sort_tree(assertion);
        assert_eq!(
            "(Bool (((BitVec 32)) ((BitVec 32) (((BitVec 32))))))",
            sort_tree.as_str()
        );
    }

    #[test]
    fn test_cb_mismatch() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (_ BitVec 16))
            |(define-ctype int (_ BitVec 32))
            |(declare-cb abs (int) int)
            |(assert (=
            |    #x00000001
            |    (abs x)
            |))
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script);
        assert!(match analyzed {
            Err(AnalyzerError::CBSignatureMismatch(_)) => true,
            _ => false,
        });
    }

    #[test]
    fn test_sort_error() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(declare-const x (Array (_ BitVec 32) (_ BitVec 8)))
            |(assert (= 
            |    #x01
            |    (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) x)
            |))
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).err().unwrap();
        assert_eq!(
            r#"SignatureMismatch(KRPKFunctionDeclare { id: Symbol("select") }, "#.to_owned()
                + r#"[KRPKGroundSort { id: Symbol("Array"), args: [KRPKGroundSort { id: Indexed("BitVec", [Numeral(8)]), "#
                + r#"args: [] }, KRPKGroundSort { id: Indexed("BitVec", [Numeral(8)]), args: [] }] }, KRPKGroundSort "#
                + r#"{ id: Symbol("Array"), args: [KRPKGroundSort { id: Indexed("BitVec", [Numeral(32)]), args: [] }, "#
                + r#"KRPKGroundSort { id: Indexed("BitVec", [Numeral(8)]), args: [] }] }])"#,
            format!("{:?}", analyzed).as_str()
        );
    }

    #[test]
    fn test_alloc_error() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(declare-const x (_ BitVec 32))
            |(alloc #x00000000 1
            |    x
            |)
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).err().unwrap();
        assert_eq!(
            "AllocOverflow(0, 1, KRPKGroundSort { id: Indexed(\"BitVec\", [Numeral(32)]), args: [] })",
            format!("{:?}", analyzed).as_str()
        );

        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(declare-const x (_ BitVec 32))
            |(declare-const y (_ BitVec 32))
            |(alloc #x00000000 4
            |    x
            |)
            |(alloc #x00000001 4
            |    x
            |)
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).err().unwrap();
        assert_eq!("AllocOverlap(0, 4, 1)", format!("{:?}", analyzed).as_str());
    }

    #[test]
    pub fn test_memory_size() {
        let script = parse_str(
            &r#"
            |(set-logic ALL)
            |(set-arch X86)
            |(declare-const x (_ BitVec 8))
            |(declare-const y (_ BitVec 8))
            |(alloc #x00000000 1 x)
            |(alloc #x00000001 4 x)
            |(check-sat)
            |(exit)
        "#
            .trim_margin()
            .unwrap(),
        )
        .unwrap();
        let mut analyzer = Analyzer::new();
        let analyzed = analyzer.analyze(&script).unwrap();
        let (min_addr, mina_size) = analyzed.memory_min_addr().unwrap();
        assert_eq!(0x0, min_addr);
        assert_eq!(1, mina_size);

        let (max_addr, maxa_size) = analyzed.memory_max_addr().unwrap();
        assert_eq!(0x1, max_addr);
        assert_eq!(4, maxa_size);

        let memory_seg_size = analyzed.memory_segment_size().unwrap();
        assert_eq!(5, memory_seg_size);
    }
}
