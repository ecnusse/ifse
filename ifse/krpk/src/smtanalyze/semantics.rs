//! Core semantic-related data structures. These data structures are semantic interpretations of SMT-LIB commands.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Debug};
use std::rc::Rc;
use std::{mem, vec};

use either::Either;

use crate::hir::{
    Binary, Decimal, Hexadecimal, Identifier as IdentifierAST, Index as IndexAST,
    MatchCase as MatchCaseAST, Numeral as NumeralAST, Pattern as PatternAST,
    QualIdentifier as QualIdentifierAST, Sort as SortAST, SortedVar as SortedVarAST, StringLiteral,
    Symbol as SymbolAST, Term as TermAST, VarBinding as VarBindingAST,
};

use super::Sorted;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KRPKIndex {
    Numeral(usize),
    Symbol(String),
}

/// An identifier either or not indexed. The id's original string form can either or not be quoted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum KRPKIdentifier {
    // We stipulate that symbols starting with `'` is for special use.
    Symbol(String),
    Indexed(String, Vec<KRPKIndex>),
}

impl PartialOrd for KRPKIdentifier {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Symbol(id1), Self::Symbol(id2)) => id1.partial_cmp(id2),
            _ => None,
        }
    }
}

impl KRPKIdentifier {
    pub fn symbol(name: &str) -> Self {
        KRPKIdentifier::Symbol(name.to_string())
    }

    pub fn numeral_indexed(name: &str, indices: &[usize]) -> Self {
        KRPKIdentifier::Indexed(
            name.to_string(),
            indices.iter().map(|idx| KRPKIndex::Numeral(*idx)).collect(),
        )
    }

    pub fn symbol_indexed(name: &str, indices: &[&str]) -> Self {
        KRPKIdentifier::Indexed(
            name.to_string(),
            indices
                .iter()
                .map(|idx| KRPKIndex::Symbol(idx.to_string()))
                .collect(),
        )
    }

    pub fn indexed(name: &str, indices: &[KRPKIndex]) -> Self {
        KRPKIdentifier::Indexed(name.to_string(), indices.to_vec())
    }
}

impl fmt::Display for KRPKIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KRPKIdentifier::Symbol(sym) => write!(f, "{}", sym),
            KRPKIdentifier::Indexed(name, indices) => {
                write!(f, "({}", name)?;
                for idx in indices.iter() {
                    match idx {
                        KRPKIndex::Numeral(num) => write!(f, " {}", num)?,
                        KRPKIndex::Symbol(sym) => write!(f, " {}", sym)?,
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

/// A generic sort with un-generic parameters.
#[derive(Clone)]
pub struct KRPKGenericSort {
    id: KRPKIdentifier,
    sort_mapping: Rc<dyn Fn(&[KRPKGroundSort]) -> Option<KRPKGroundSort>>,
}

impl PartialEq for KRPKGenericSort {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Debug for KRPKGenericSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KRPKGenericSort")
            .field("id", &self.id)
            .finish()
    }
}

impl KRPKGenericSort {
    pub fn instantiate(&self, args: &[KRPKGroundSort]) -> Option<KRPKGroundSort> {
        (self.sort_mapping)(args)
    }
}

/// A vanilla sort without any generic parameters or with all generic parameters instantiated.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KRPKGroundSort {
    id: KRPKIdentifier,
    args: Vec<KRPKGroundSort>,
}

impl KRPKGroundSort {
    pub fn new(id: KRPKIdentifier, args: Vec<KRPKGroundSort>) -> Self {
        KRPKGroundSort { id, args }
    }
    fn to_intrinsic(&self) -> IntrinsicSort {
        match self.id {
            KRPKIdentifier::Symbol(ref name) => match name.as_str() {
                "Bool" => {
                    if self.args.len() != 0 {
                        panic!("Unexpected args: {:?}", self.args);
                    }
                    IntrinsicSort::Bool
                }
                "Array" => match self.args.as_slice() {
                    [ref domain, ref range] => IntrinsicSort::Array(
                        Box::new(domain.to_intrinsic()),
                        Box::new(range.to_intrinsic()),
                    ),
                    _ => panic!("Unexpected args: {:?}", self.args),
                },
                _ => panic!("Unexpected symbol: {}", name),
            },
            KRPKIdentifier::Indexed(ref name, ref indices) => match name.as_str() {
                "BitVec" => match indices.as_slice() {
                    [KRPKIndex::Numeral(size)] => IntrinsicSort::BitVec(*size),
                    _ => panic!("Unexpected indices: {:?}", indices),
                },
                _ => panic!("Unexpected symbol: {}", name),
            },
        }
    }

    pub fn is_bool(&self) -> bool {
        match self.to_intrinsic() {
            IntrinsicSort::Bool => true,
            _ => false,
        }
    }

    pub fn is_bit_vec(&self) -> bool {
        match self.to_intrinsic() {
            IntrinsicSort::BitVec(_) => true,
            _ => false,
        }
    }

    pub fn bit_vec_width(&self) -> Option<usize> {
        match self.to_intrinsic() {
            IntrinsicSort::BitVec(size) => Some(size),
            _ => None,
        }
    }

    pub fn is_array(&self) -> bool {
        match self.to_intrinsic() {
            IntrinsicSort::Array(_, _) => true,
            _ => false,
        }
    }

    pub fn array_domain(&self) -> Option<KRPKGroundSort> {
        match self.to_intrinsic() {
            IntrinsicSort::Array(domain, _) => Some((*domain).into()),
            _ => None,
        }
    }

    pub fn array_range(&self) -> Option<KRPKGroundSort> {
        match self.to_intrinsic() {
            IntrinsicSort::Array(_, range) => Some((*range).into()),
            _ => None,
        }
    }
}

impl fmt::Display for KRPKGroundSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.id)
        } else {
            write!(f, "({}", self.id)?;
            for arg in self.args.iter() {
                write!(f, " {}", arg)?;
            }
            write!(f, ")")
        }
    }
}

fn bool_sort() -> KRPKGroundSort {
    KRPKGroundSort {
        id: KRPKIdentifier::symbol("Bool"),
        args: vec![],
    }
}

fn bv_sort(size: usize) -> KRPKGroundSort {
    KRPKGroundSort {
        id: KRPKIdentifier::numeral_indexed("BitVec", &[size]),
        args: vec![],
    }
}

fn array_sort() -> KRPKGenericSort {
    KRPKGenericSort {
        id: KRPKIdentifier::symbol("Array"),
        sort_mapping: Rc::new(|args| match args {
            [domain, range] => Some(KRPKGroundSort {
                id: KRPKIdentifier::symbol("Array"),
                args: vec![domain.clone(), range.clone()],
            }),
            _ => None,
        }),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SortError {
    Undefined(SortAST),
    NotInstantiated(SortAST, Vec<SortError>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CTypeError {
    ImproperCTypeID(SymbolAST),
    SortError(SortError),
    Undefined(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionError {
    Undefined(KRPKIdentifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionDeclarationError {
    Conflicted(KRPKIdentifier),
    SortError(SortError),
    CTypeError(CTypeError),
}

/// Auxiliary data structure for [`KRPKGroundSort`]. Only for internal use.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum IntrinsicSort {
    Bool,
    BitVec(usize),
    Array(Box<IntrinsicSort>, Box<IntrinsicSort>),
}

impl From<IntrinsicSort> for KRPKGroundSort {
    fn from(s: IntrinsicSort) -> Self {
        match s {
            IntrinsicSort::Bool => bool_sort(),
            IntrinsicSort::BitVec(size) => bv_sort(size),
            IntrinsicSort::Array(first, second) => array_sort()
                .instantiate(&[(*first).into(), (*second).into()])
                .unwrap(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum KRPKLogic {
    Core,
    All,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum KRPKArch {
    X86,
}

/// A function declaration, consisting with an id and a mapping that maps the args' sorts, and in the case where the return sort
/// involves polymorphism, with the restricted return sort, to the return sort.
#[derive(Clone)]
pub struct KRPKFunctionDeclaration {
    pub id: KRPKIdentifier,

    /// Mapping the args' sorts to the return sort. Return None if the args' sorts do not match the function's signature.
    /// The mapping is in the form of `(ArgSort, ...) -> ReturnSort`. When the result coercion sort is needed (in cases like `((func as CoercionSort) arg...)`),
    /// It it in the form of `(ArgSort, ..., CoercionSort) -> ReturnSort`
    pub(super) sort_mapping: Rc<dyn Fn(&[KRPKGroundSort]) -> Option<KRPKGroundSort>>,
}

impl PartialEq for KRPKFunctionDeclaration {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Debug for KRPKFunctionDeclaration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KRPKFunctionDeclare")
            .field("id", &self.id)
            .finish()
    }
}

impl KRPKFunctionDeclaration {
    /// Get the result sort from the args' sorts. Return `None` if the args' sorts do not match the function's signature.
    pub fn map_sort(&self, args: &[KRPKGroundSort]) -> Option<KRPKGroundSort> {
        (self.sort_mapping)(args)
    }
}

/// A maybe qualified identifier. When qualified, the identifier's type is polymorphic and restricted by a reified sort.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum KRPKQualIdentifier {
    Simple(KRPKIdentifier),
    Qualified(KRPKIdentifier, KRPKGroundSort),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum KRPKSpecConstant {
    Numeral(usize),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum KRPKPattern {
    Identifier(KRPKIdentifier),
    Constructor(KRPKIdentifier, Vec<KRPKIdentifier>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct KRPKMatchCase {
    pub pattern: Sorted<KRPKPattern>,
    pub body: Sorted<KRPKTerm>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum KRPKTerm {
    SpecConstant(KRPKSpecConstant),
    Identifier(KRPKQualIdentifier),
    Let(
        Vec<(KRPKIdentifier, Sorted<KRPKTerm>)>,
        Sorted<Box<KRPKTerm>>,
    ),
    Forall(Vec<(KRPKIdentifier, KRPKGroundSort)>, Sorted<Box<KRPKTerm>>),
    Exists(Vec<(KRPKIdentifier, KRPKGroundSort)>, Sorted<Box<KRPKTerm>>),
    Match(Sorted<Box<KRPKTerm>>, Vec<Sorted<KRPKMatchCase>>),
    Apply(KRPKQualIdentifier, Vec<Sorted<KRPKTerm>>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum KRPKFunction {
    Predefined(KRPKFunctionDeclaration),
    DeclaredConstant(KRPKFunctionDeclaration),
    CBFunction(KRPKCBFunctionDecl),
}

/// A close-box function's declaration, consisting with an id, a list of params, and a return sort-and-type pair.
/// Each param is described by a (SMT-LIB)sort-and-(C)type pair. The sort and the type should corresponds.
/// For example, `(_ BitVec 8) <-> char` but not `(_ BitVec 8) <-> long`. So is the return sort-and-type pair.
#[derive(Clone, Debug, PartialEq, Hash)]
pub struct KRPKCBFunctionDecl {
    pub id: KRPKIdentifier,
    pub params: Vec<(KRPKGroundSort, String)>,
    pub return_sort_and_type: (KRPKGroundSort, String),
}

impl KRPKCBFunctionDecl {
    pub fn map_sort(&self, args: &[KRPKGroundSort]) -> Option<KRPKGroundSort> {
        if args.len() != self.params.len() {
            return None;
        }
        for (arg, param) in args.iter().zip(self.params.iter()) {
            if arg != &param.0 {
                return None;
            }
        }
        Some(self.return_sort_and_type.0.clone())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AllocError {
    ReAlloc(u64),
}

/// An environment that interpret SMT-LIB syntactic constructs to semantic objects.
pub struct KRPKEnvironment {
    logic: KRPKLogic,

    arch: Option<KRPKArch>,

    memory: BTreeMap<u64, (usize, Either<Sorted<KRPKTerm>, String>)>,
    implicit_min_addr: Option<(u64, usize)>,
    implicit_max_addr: Option<(u64, usize)>,

    // TODO: Support assertion stack?
    /// Assertions to check.
    assertions: Vec<Sorted<KRPKTerm>>,

    /// User-defined functions, theoretically including constants (functions with zero params) and other functions (with more than zero params).
    /// However, we currently only support constants.
    user_functions: HashMap<KRPKIdentifier, KRPKFunction>,

    /// Upper bounds of a bit-vector array's indices, converted to an unsigned value. Note that we do not support
    /// other general kind arrays.
    array_index_bound: HashMap<KRPKIdentifier, u64>,

    /// C type to SMT-LIB sort corresponding.
    ctypes: HashMap<String, KRPKGroundSort>,

    // The following are caches for efficiency.
    function_cache: RefCell<HashMap<KRPKIdentifier, KRPKFunction>>,
    symbol_cache: RefCell<HashMap<SymbolAST, String>>,
    index_cache: RefCell<HashMap<IndexAST, KRPKIndex>>,
    identifier_cache: RefCell<HashMap<IdentifierAST, KRPKIdentifier>>,
    sort_cache: RefCell<HashMap<SortAST, KRPKGroundSort>>,
}

impl KRPKEnvironment {
    pub fn new() -> Self {
        Self::with_logic(KRPKLogic::Core)
    }

    pub fn with_logic(logic: KRPKLogic) -> Self {
        KRPKEnvironment {
            logic,
            arch: None,
            memory: Default::default(),
            assertions: vec![],
            user_functions: HashMap::new(),
            ctypes: HashMap::new(),
            array_index_bound: HashMap::new(),
            function_cache: RefCell::new(HashMap::new()),
            symbol_cache: RefCell::new(HashMap::new()),
            index_cache: RefCell::new(HashMap::new()),
            identifier_cache: RefCell::new(HashMap::new()),
            sort_cache: RefCell::new(HashMap::new()),
            implicit_max_addr: Default::default(),
            implicit_min_addr: Default::default(),
        }
    }

    pub fn update_array_index_bound(&mut self, array_id: &KRPKIdentifier, bound: u64) -> bool {
        let old = self
            .array_index_bound
            .entry(array_id.clone())
            .or_insert(0u64);
        if *old < bound {
            *old = bound;
            true
        } else {
            false
        }
    }

    pub fn get_array_index_bound(&self, array_id: &KRPKIdentifier) -> Option<u64> {
        self.array_index_bound.get(array_id).cloned()
    }

    pub fn reset_assertions(&mut self) -> Vec<Sorted<KRPKTerm>> {
        mem::take(&mut self.assertions)
    }

    pub fn reset_memory(&mut self) -> BTreeMap<u64, (usize, Either<Sorted<KRPKTerm>, String>)> {
        mem::take(&mut self.memory)
    }

    pub fn set_logic(&mut self, logic: KRPKLogic) -> KRPKLogic {
        let old = self.logic;
        self.logic = logic;
        old
    }

    pub fn set_arch(&mut self, arch: KRPKArch) -> Option<KRPKArch> {
        let old = self.arch;
        self.arch = Some(arch);
        old
    }

    pub fn arch(&self) -> Option<KRPKArch> {
        self.arch
    }

    pub fn memory_allocs(
        &self,
    ) -> impl Iterator<Item = (&u64, &usize, &Either<Sorted<KRPKTerm>, String>)> {
        self.memory
            .iter()
            .map(|(addr, (size, value))| (addr, size, value))
    }

    pub fn memory_max_addr(&self) -> Option<(u64, usize)> {
        let explicit = self
            .memory
            .iter()
            .max_by_key(|(addr, _)| *addr)
            .map(|(addr, (size, _))| (*addr, *size));
        let implicit = self.implicit_max_addr;
        match (explicit, implicit) {
            (None, None) => None,
            (p1 @ Some((addr1, sz1)), p2 @ Some((addr2, sz2))) => {
                if addr1 + (sz1 as u64) > addr2 + (sz2 as u64) {
                    p1
                } else {
                    p2
                }
            }
            (_, p @ Some(..)) => p,
            (p @ Some(..), _) => p,
        }
    }

    pub fn memory_min_addr(&self) -> Option<(u64, usize)> {
        let explicit = self
            .memory
            .iter()
            .min_by_key(|(addr, _)| *addr)
            .map(|(addr, (size, _))| (*addr, *size));
        let implicit = self.implicit_min_addr;
        match (explicit, implicit) {
            (None, None) => None,
            (p1 @ Some((addr1, _)), p2 @ Some((addr2, _))) => {
                if addr1 < addr2 {
                    p1
                } else {
                    p2
                }
            }
            (_, p @ Some(..)) => p,
            (p @ Some(..), _) => p,
        }
    }

    pub fn get_alloc(&self, addr: u64) -> Option<(usize, &Either<Sorted<KRPKTerm>, String>)> {
        self.memory.get(&addr).map(|(size, term)| (*size, term))
    }

    pub fn size_of(&self, sort: &KRPKGroundSort) -> Option<usize> {
        match sort.to_intrinsic() {
            IntrinsicSort::Bool => Some(1),
            IntrinsicSort::BitVec(size) => Some(size / 8 + if size % 8 == 0 { 0 } else { 1 }),
            IntrinsicSort::Array(_, _) => None,
        }
    }

    pub fn alloc(
        &mut self,
        addr: &u64,
        alloc_size: usize,
        term: Sorted<KRPKTerm>,
    ) -> Result<(), AllocError> {
        let r = self.memory.insert(*addr, (alloc_size, Either::Left(term)));
        if r.is_some() {
            Err(AllocError::ReAlloc(*addr))
        } else {
            Ok(())
        }
    }

    pub fn alloc_seg(
        &mut self,
        addr: &u64,
        alloc_size: usize,
        hex_bytes: &str,
    ) -> Result<(), AllocError> {
        let r = self
            .memory
            .insert(*addr, (alloc_size, Either::Right(hex_bytes.to_string())));
        if r.is_some() {
            Err(AllocError::ReAlloc(*addr))
        } else {
            Ok(())
        }
    }

    pub fn reserve_addr(&mut self, addr: &u64, alloc_size: usize) {
        self.implicit_min_addr = Some(self.implicit_min_addr.map_or(
            (*addr, alloc_size),
            |p @ (old_addr, _)| {
                if old_addr > *addr {
                    (*addr, alloc_size)
                } else {
                    p
                }
            },
        ));
        self.implicit_max_addr = Some(self.implicit_max_addr.map_or(
            (*addr, alloc_size),
            |p @ (old_addr, old_sz)| {
                if old_addr + (old_sz as u64) < *addr + (alloc_size as u64) {
                    (*addr, alloc_size)
                } else {
                    p
                }
            },
        ));
    }

    pub fn memory_segment_size(&self) -> Option<u64> {
        match (self.memory_max_addr(), self.memory_min_addr()) {
            (Some((max_addr, max_addr_size)), Some((min_addr, _))) => {
                Some(max_addr - min_addr + max_addr_size as u64)
            }
            (None, None) => None,
            _ => unreachable!(),
        }
    }

    pub fn assertions(&self) -> &[Sorted<KRPKTerm>] {
        &self.assertions
    }

    pub fn interpret_numeral(&self, num: &NumeralAST) -> usize {
        num.0
    }

    pub fn interpret_hex(&self, hex: &Hexadecimal) -> (usize, Option<u64>) {
        (hex.digit_num * 4, hex.value())
    }

    pub(super) fn interpret_term(&self, term_ast: &TermAST) -> Sorted<KRPKTerm> {
        match term_ast {
            TermAST::SpecConstant(spec_constant) => match spec_constant {
                crate::hir::SpecConstant::Numeral(num) => {
                    let NumeralAST(num) = num;
                    Sorted::new(KRPKTerm::SpecConstant(KRPKSpecConstant::Numeral(*num)))
                }
                crate::hir::SpecConstant::Hexadecimal(hex) => Sorted::new(KRPKTerm::SpecConstant(
                    KRPKSpecConstant::Hexadecimal(hex.clone()),
                )),
                crate::hir::SpecConstant::Binary(bin) => Sorted::new(KRPKTerm::SpecConstant(
                    KRPKSpecConstant::Binary(bin.clone()),
                )),
                crate::hir::SpecConstant::Decimal(dec) => Sorted::new(KRPKTerm::SpecConstant(
                    KRPKSpecConstant::Decimal(dec.clone()),
                )),
                crate::hir::SpecConstant::StringLiteral(literal) => {
                    let StringLiteral(s) = literal;
                    Sorted::new(KRPKTerm::SpecConstant(KRPKSpecConstant::String(s.clone())))
                }
            },
            TermAST::QualIdentifier(qi) => match qi {
                QualIdentifierAST::Simple(id) => {
                    let id = self.interpret_identifier(id);
                    Sorted::new(KRPKTerm::Identifier(KRPKQualIdentifier::Simple(id)))
                }
                QualIdentifierAST::Qualified(id, sort) => {
                    let id = self.interpret_identifier(id);
                    let sort = self.interpret_sort(sort).unwrap();
                    Sorted::new(KRPKTerm::Identifier(KRPKQualIdentifier::Qualified(
                        id, sort,
                    )))
                }
            },
            TermAST::Let(bindings_ast, inner) => {
                let mut bindings = vec![];
                for b in bindings_ast {
                    let VarBindingAST(sym, bound_term) = b;
                    let sym = self.interpret_symbol(sym);
                    let id = KRPKIdentifier::symbol(&sym);
                    let bound_term = self.interpret_term(bound_term);
                    bindings.push((id, bound_term));
                }
                let inner = self.interpret_term(&inner.clone());
                Sorted::new(KRPKTerm::Let(bindings, inner.map_inner(Box::new)))
            }
            TermAST::Forall(sorted_vars_ast, inner) => {
                let mut sort_bindings = vec![];
                for sv in sorted_vars_ast {
                    let SortedVarAST(sym, sort) = sv;
                    let sym = self.interpret_symbol(sym);
                    let sort = self.interpret_sort(sort).unwrap();
                    sort_bindings.push((KRPKIdentifier::symbol(&sym), sort));
                }
                let inner = self.interpret_term(&inner.clone());
                Sorted::new(KRPKTerm::Forall(sort_bindings, inner.map_inner(Box::new)))
            }
            TermAST::Exists(sorted_vars_ast, inner) => {
                let mut sort_bindings = vec![];
                for sv in sorted_vars_ast {
                    let SortedVarAST(sym, sort) = sv;
                    let sym = self.interpret_symbol(sym);
                    let sort = self.interpret_sort(sort).unwrap();
                    sort_bindings.push((KRPKIdentifier::symbol(&sym), sort));
                }
                let inner = self.interpret_term(&inner.clone());
                Sorted::new(KRPKTerm::Exists(sort_bindings, inner.map_inner(Box::new)))
            }
            TermAST::Match(inner, matches) => {
                let inner = self.interpret_term(&inner.clone());
                let mut cases = vec![];
                for m in matches {
                    let MatchCaseAST(pattern, body) = m;
                    let pattern = Sorted::new(match pattern {
                        PatternAST::Simple(symbol) => {
                            // KRPKPattern::Identifier(self.identifier(id))
                            let sym = self.interpret_symbol(symbol);
                            KRPKPattern::Identifier(KRPKIdentifier::symbol(&sym))
                        }
                        PatternAST::Constructor(symbol, args) => {
                            let id = {
                                let sym = self.interpret_symbol(symbol);
                                KRPKIdentifier::symbol(&sym)
                            };
                            let args = args
                                .iter()
                                .map(|symbol| {
                                    let sym = self.interpret_symbol(symbol);
                                    KRPKIdentifier::symbol(&sym)
                                })
                                .collect();
                            KRPKPattern::Constructor(id, args)
                        }
                    });
                    let body = self.interpret_term(body);
                    cases.push(Sorted::new(KRPKMatchCase { pattern, body }));
                }
                Sorted::new(KRPKTerm::Match(inner.map_inner(Box::new), cases))
            }
            TermAST::Annotated(inner, _) => self.interpret_term(&inner.clone()),
            TermAST::Apply(qid, inner) => {
                let qid = match qid {
                    QualIdentifierAST::Simple(id) => {
                        let id = self.interpret_identifier(id);
                        KRPKQualIdentifier::Simple(id)
                    }
                    QualIdentifierAST::Qualified(id, sort) => {
                        let id = self.interpret_identifier(id);
                        let sort = self.interpret_sort(sort).unwrap();
                        KRPKQualIdentifier::Qualified(id, sort)
                    }
                };
                let inner = inner
                    .iter()
                    .map(|t| self.interpret_term(t))
                    .collect::<Vec<_>>();
                Sorted::new(KRPKTerm::Apply(qid, inner))
            }
        }
    }

    pub fn interpret_index(&self, index_ast: &IndexAST) -> KRPKIndex {
        {
            let tmp = self.index_cache.borrow();
            let index_cached = tmp.get(index_ast);
            if let Some(i) = index_cached {
                return i.clone();
            }
        }
        let i = match index_ast {
            IndexAST::Numeral(num) => KRPKIndex::Numeral(self.interpret_numeral(num)),
            IndexAST::Symbol(sym) => KRPKIndex::Symbol(self.interpret_symbol(sym)),
        };
        let r = self
            .index_cache
            .borrow_mut()
            .insert(index_ast.clone(), i.clone());
        assert!(r.is_none());
        i
    }

    pub fn interpret_const_declaration(
        &self,
        const_name: &SymbolAST,
        sort: &SortAST,
    ) -> Result<KRPKFunction, FunctionDeclarationError> {
        let symbol = self.interpret_symbol(const_name);
        let id = KRPKIdentifier::symbol(&symbol);
        let return_sort = self
            .interpret_sort(sort)
            .map_err(|err| FunctionDeclarationError::SortError(err))?;

        let sort_mapping = Rc::new(move |args: &[KRPKGroundSort]| {
            if args.len() == 0 {
                Some(return_sort.clone())
            } else {
                None
            }
        });
        Ok(KRPKFunction::DeclaredConstant(KRPKFunctionDeclaration {
            id,
            sort_mapping,
        }))
    }

    pub fn user_functions(&self) -> impl Iterator<Item = &KRPKFunction> {
        self.user_functions.values()
    }

    pub fn interpret_ctype_definition(
        &self,
        ctype: &SymbolAST,
        sort: &SortAST,
    ) -> Result<(KRPKGroundSort, String), CTypeError> {
        let ctype1 = self.interpret_symbol(ctype);
        // let pattern = regex::Regex::new(r"^[a-zA-Z_][a-zA-Z_0-9]*$").unwrap();
        // if !pattern.is_match(&ctype1) {
        //     return Err(CTypeError::ImproperCTypeID(ctype.clone()));
        // }
        let sort = self
            .interpret_sort(sort)
            .map_err(|err| CTypeError::SortError(err))?;
        Ok((sort, ctype1))
    }

    pub fn lookup_ctype(&self, ctype: &str) -> Result<KRPKGroundSort, CTypeError> {
        self.ctypes
            .get(ctype)
            .map(|s| s.clone())
            .ok_or(CTypeError::Undefined(ctype.to_owned()))
    }

    pub fn ctypes(&self) -> Vec<(&str, &KRPKGroundSort)> {
        self.ctypes
            .iter()
            .map(|(ctype, sort)| (ctype.as_str(), sort))
            .collect()
    }

    pub fn define_ctype(
        &mut self,
        ctype: &SymbolAST,
        sort: &SortAST,
    ) -> Result<(KRPKGroundSort, String), CTypeError> {
        let (sort, name) = self.interpret_ctype_definition(ctype, sort)?;
        let _r = self.ctypes.insert(name.clone(), sort.clone());
        Ok((sort, name))
    }

    pub fn interpret_cb_declaration(
        &self,
        cb_name: &SymbolAST,
        param_types: &[SymbolAST],
        return_type: &SymbolAST,
    ) -> Result<KRPKFunction, FunctionDeclarationError> {
        let symbol1 = self.interpret_symbol(cb_name);
        let id = KRPKIdentifier::symbol(&symbol1);

        let mut params = vec![];
        for param_type in param_types {
            let param_type = self.interpret_symbol(param_type);
            let param_sort = self
                .lookup_ctype(&param_type)
                .map_err(|err| FunctionDeclarationError::CTypeError(err))?;
            params.push((param_sort, param_type));
        }

        let return_type = self.interpret_symbol(return_type);
        let return_sort = self
            .lookup_ctype(&return_type)
            .map_err(|err| FunctionDeclarationError::CTypeError(err))?;
        Ok(KRPKFunction::CBFunction(KRPKCBFunctionDecl {
            id: id.clone(),
            params,
            return_sort_and_type: (return_sort, return_type),
        }))
    }

    pub fn is_pointer(&self, ctype: &str) -> bool {
        ctype.ends_with("*")
    }

    pub fn declare_cb(
        &mut self,
        cb_name: &SymbolAST,
        param_types: &[SymbolAST],
        return_type: &SymbolAST,
    ) -> Result<KRPKFunction, FunctionDeclarationError> {
        let symbol1 = self.interpret_symbol(cb_name);
        let id = KRPKIdentifier::symbol(&symbol1);
        if self.user_functions.contains_key(&id) {
            return Err(FunctionDeclarationError::Conflicted(id));
        }

        let decl = self.interpret_cb_declaration(cb_name, param_types, return_type)?;

        let r = self.user_functions.insert(id, decl.clone());
        assert!(r.is_none());
        Ok(decl)
    }

    pub fn declare_const(
        &mut self,
        const_name: &SymbolAST,
        sort: &SortAST,
    ) -> Result<KRPKFunction, FunctionDeclarationError> {
        let symbol1 = self.interpret_symbol(const_name);
        let id = KRPKIdentifier::symbol(&symbol1);
        if self.user_functions.contains_key(&id) {
            return Err(FunctionDeclarationError::Conflicted(id));
        }
        let f = self.interpret_const_declaration(const_name, sort)?;
        let r = self.user_functions.insert(id, f.clone());
        assert!(r.is_none());
        Ok(f)
    }

    pub fn push_assertion(&mut self, assertion: Sorted<KRPKTerm>) {
        self.assertions.push(assertion)
    }

    /// Return the bool sort.
    pub fn bool_sort(&self) -> KRPKGroundSort {
        bool_sort()
    }

    /// Get the semantic identifier object corresponding to a symbol ast.
    pub fn interpret_symbol(&self, symbol: &SymbolAST) -> String {
        {
            let tmp = self.symbol_cache.borrow();
            let symbol_cached = tmp.get(symbol);
            if let Some(s) = symbol_cached {
                return s.clone();
            }
        }
        let s = match symbol {
            SymbolAST::Simple(tmp) => tmp.clone(),
            SymbolAST::Quoted(tmp) => tmp.clone(),
        };
        let r = self
            .symbol_cache
            .borrow_mut()
            .insert(symbol.clone(), s.clone());
        assert!(r.is_none());
        s
    }

    /// Get the semantic identifier object corresponding to an identifier ast.
    pub fn interpret_identifier(&self, ident: &IdentifierAST) -> KRPKIdentifier {
        {
            let tmp = self.identifier_cache.borrow();
            let identifier_cached = tmp.get(ident);
            if let Some(i) = identifier_cached {
                return i.clone();
            }
        }
        let i = match ident {
            IdentifierAST::Symbol(sym) => KRPKIdentifier::Symbol(self.interpret_symbol(sym)),
            IdentifierAST::Indexed(sym, indices) => {
                let id = self.interpret_symbol(sym);
                let indices = indices
                    .iter()
                    .map(|idx| self.interpret_index(idx))
                    .collect::<Vec<_>>();
                KRPKIdentifier::Indexed(id, indices)
            }
        };
        let r = self
            .identifier_cache
            .borrow_mut()
            .insert(ident.clone(), i.clone());
        assert!(r.is_none());
        i
    }

    fn core_sort(&self, sort_ast: &SortAST) -> Result<KRPKGroundSort, SortError> {
        match sort_ast {
            SortAST::Simple(id) => {
                let id = self.interpret_identifier(id);
                match id {
                    KRPKIdentifier::Symbol(sym) => {
                        if "Bool" == sym {
                            Ok(bool_sort())
                        } else {
                            Err(SortError::Undefined(sort_ast.clone()))
                        }
                    }
                    _ => Err(SortError::Undefined(sort_ast.clone())),
                }
            }
            _ => Err(SortError::Undefined(sort_ast.clone())),
        }
    }

    fn qf_bv_sort(&self, sort_ast: &SortAST) -> Result<KRPKGroundSort, SortError> {
        match sort_ast {
            SortAST::Simple(id) => {
                let id = self.interpret_identifier(id);
                match id {
                    KRPKIdentifier::Indexed(sym, indices) => {
                        if "BitVec" == sym {
                            match indices.as_slice() {
                                [KRPKIndex::Numeral(size)] => Ok(bv_sort(*size)),
                                _ => Err(SortError::Undefined(sort_ast.clone())),
                            }
                        } else {
                            Err(SortError::Undefined(sort_ast.clone()))
                        }
                    }
                    _ => Err(SortError::Undefined(sort_ast.clone())),
                }
            }
            _ => Err(SortError::Undefined(sort_ast.clone())),
        }
    }

    fn arrays_ex_sort(&self, sort_ast: &SortAST) -> Result<KRPKGroundSort, SortError> {
        match sort_ast {
            SortAST::Parametric(id, args) => {
                let id = self.interpret_identifier(id);
                match id {
                    KRPKIdentifier::Symbol(sym) => {
                        if "Array" == sym {
                            match args.as_slice() {
                                [domain, range] => {
                                    let domain = self.interpret_sort(domain);
                                    let range = self.interpret_sort(range);
                                    match (domain, range) {
                                        (Err(e1), Err(e2)) => Err(SortError::NotInstantiated(
                                            sort_ast.clone(),
                                            vec![e1, e2],
                                        )),
                                        (Err(e), _) => Err(SortError::NotInstantiated(
                                            sort_ast.clone(),
                                            vec![e],
                                        )),
                                        (_, Err(e)) => Err(SortError::NotInstantiated(
                                            sort_ast.clone(),
                                            vec![e],
                                        )),
                                        (Ok(domain), Ok(range)) => {
                                            Ok(array_sort().instantiate(&[domain, range]).unwrap())
                                        }
                                    }
                                }
                                _ => Err(SortError::Undefined(sort_ast.clone())),
                            }
                        } else {
                            Err(SortError::Undefined(sort_ast.clone()))
                        }
                    }
                    _ => Err(SortError::Undefined(sort_ast.clone())),
                }
            }
            _ => Err(SortError::Undefined(sort_ast.clone())),
        }
    }

    pub fn logic(&self) -> KRPKLogic {
        self.logic
    }

    /// Get the semantic sort object corresponding to a sort ast.
    pub fn interpret_sort(&self, sort_ast: &SortAST) -> Result<KRPKGroundSort, SortError> {
        {
            let tmp = self.sort_cache.borrow();
            let cached = tmp.get(sort_ast);
            if let Some(s) = cached {
                return Ok(s.clone());
            }
        }
        let s = match self.logic {
            KRPKLogic::All => Self::chain_in_order(
                &[Self::arrays_ex_sort, Self::qf_bv_sort, Self::core_sort],
                self,
                sort_ast,
                |err| match err {
                    SortError::Undefined(_) => true,
                    _ => false,
                },
            ),
            KRPKLogic::Core => {
                Self::chain_in_order(&[Self::core_sort], self, sort_ast, |err| match err {
                    SortError::Undefined(_) => true,
                    _ => false,
                })
            }
        }?;
        let r = self
            .sort_cache
            .borrow_mut()
            .insert(sort_ast.clone(), s.clone());
        assert!(r.is_none());
        Ok(s)
    }

    fn qf_bv_constant(&self, const_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        match const_id {
            KRPKIdentifier::Indexed(name, indices) => {
                // TODO: Support the`[[#bY]]` extension?

                let num = match indices.as_slice() {
                    [KRPKIndex::Numeral(num)] => *num,
                    _ => return Err(FunctionError::Undefined(const_id.clone())),
                };

                // Support `(_ bvX n)`.
                let pattern = regex::Regex::new(r"^bv(\d+)$").unwrap();
                let decl = if let Some(captures) = pattern.captures(name.as_str()) {
                    let size = captures.get(1).unwrap().as_str().parse::<usize>().unwrap();
                    KRPKFunctionDeclaration {
                        id: KRPKIdentifier::numeral_indexed("'n2bv", &[size, num]), // A special intrinsic function
                        sort_mapping: Rc::new(move |args| match args {
                            [] => Some(IntrinsicSort::BitVec(size).into()),
                            _ => None,
                        }),
                    }
                } else {
                    return Err(FunctionError::Undefined(const_id.clone()));
                };
                Ok(KRPKFunction::Predefined(decl))
            }
            KRPKIdentifier::Symbol(_) => Err(FunctionError::Undefined(const_id.clone())),
        }
    }

    fn user_function(&self, func_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        match self.user_functions.get(func_id) {
            Some(s) => {
                assert!(match s {
                    KRPKFunction::DeclaredConstant(_) | KRPKFunction::CBFunction(_) => true,
                    _ => false,
                });
                Ok(s.clone())
            }
            None => Err(FunctionError::Undefined(func_id.clone())),
        }
    }

    /// Return the function with some special id (`identifier`). Currently not support user-defined functions.
    pub fn lookup_function(&self, func_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        {
            let tmp = self.function_cache.borrow();
            let cached = tmp.get(func_id);
            if let Some(f) = cached {
                return Ok(f.clone());
            }
        }
        let f = match self.logic {
            KRPKLogic::All => Self::chain_in_order(
                &[
                    Self::user_function,
                    Self::core_constant,
                    Self::core_function,
                    Self::qf_bv_constant,
                    Self::qf_bv_function,
                    Self::arrays_ex_function,
                    Self::core_function,
                ],
                self,
                func_id,
                |err| match err {
                    FunctionError::Undefined(_) => true,
                },
            ),
            KRPKLogic::Core => Self::chain_in_order(
                &[Self::user_function, Self::core_function],
                self,
                func_id,
                |err| match err {
                    FunctionError::Undefined(_) => true,
                },
            ),
        }?;
        let r = self
            .function_cache
            .borrow_mut()
            .insert(func_id.clone(), f.clone());
        assert!(r.is_none());
        Ok(f)
    }

    fn chain_in_order<T, R, Err: PartialEq + Clone, F: Fn(&Err) -> bool>(
        funcs: &[fn(&Self, &T) -> Result<R, Err>],
        the_self: &Self,
        arg: &T,
        try_next: F,
    ) -> Result<R, Err> {
        let mut final_err = None;
        for f in funcs {
            match f(the_self, arg) {
                Err(ref e) => {
                    final_err = Some(e.clone());
                    if try_next(e) {
                        continue;
                    }
                    return Err(e.clone());
                }
                ok @ Ok(_) => return ok,
            }
        }
        Err(final_err.unwrap())
    }

    fn core_constant(&self, const_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        let KRPKIdentifier::Symbol(name) = const_id else {
            return Err(FunctionError::Undefined(const_id.clone()));
        };
        match name.as_str() {
            "true" | "false" => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                id: const_id.clone(),
                sort_mapping: Rc::new(|args| {
                    if !args.is_empty() {
                        None
                    } else {
                        Some(bool_sort())
                    }
                }),
            })),
            _ => Err(FunctionError::Undefined(const_id.clone())),
        }
    }

    fn core_function(&self, func_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        match func_id {
            KRPKIdentifier::Symbol(name) => {
                match_template! {
                    LEAST_BINARY = ["=>", "and", "or", "xor"], // Arguments >= 2
                    SEPCIAL_FIRST = ["=", "distinct"], // Arguments >= 2 && Special treatment fot First

                    match name.as_str() {
                        LEAST_BINARY => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| {
                                    if args.len() < 2 {
                                        return None;
                                    }
                                    if args.iter().all(|arg| arg.is_bool()) {
                                        Some(bool_sort())
                                    } else {
                                        None
                                    }
                                }),
                            }))
                        },
                        SEPCIAL_FIRST => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| {
                                    if args.len() < 2 {
                                        return None;
                                    }
                                    let first = &args[0];
                                    if args[1..].iter().all(|s| s == first) {
                                        Some(bool_sort())
                                    } else {
                                        None
                                    }
                                }),
                            }))
                        },
                        "not" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [arg] => {
                                        if arg.is_bool() {
                                            Some(bool_sort())
                                        } else {
                                            None
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "ite" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [arg1, arg2, arg3] => {
                                        if arg1.is_bool() && arg2 == arg3 {
                                            Some(arg2.clone())
                                        } else {
                                            None
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    }
                }
            }
            KRPKIdentifier::Indexed(_, _) => Err(FunctionError::Undefined(func_id.clone())),
        }
    }

    fn qf_bv_function(&self, func_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        match func_id {
            KRPKIdentifier::Symbol(name) => {
                match_template! {
                    UNARY = ["bvnot", "bvneg"],
                    BINARY = ["bvudiv", "bvurem", "bvshl", "bvlshr", "bvnand", "bvnor",
                              "bvxnor", "bvsub", "bvsdiv", "bvsrem", "bvsmod", "bvashr"],
                    LEFT_ASSOC = ["bvand", "bvor", "bvadd", "bvmul"],
                    COMPARE_PREDICATE = ["bvult", "bvule", "bvugt", "bvuge",
                               "bvslt", "bvsle", "bvsgt", "bvsge"],

                    match name.as_str() {
                        UNARY => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [first] => {
                                        let first = first.to_intrinsic();
                                        match first {
                                            IntrinsicSort::BitVec(i) => Some(IntrinsicSort::BitVec(i).into()),
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        BINARY => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                            id: func_id.clone(),
                            sort_mapping: Rc::new(|args| match args {
                                [first, second] => {
                                    let first = first.to_intrinsic();
                                    let second = second.to_intrinsic();
                                    match (first, second) {
                                        (IntrinsicSort::BitVec(i), IntrinsicSort::BitVec(j)) => {
                                            if i == j {
                                                Some(IntrinsicSort::BitVec(i).into())
                                            } else {
                                                None
                                            }
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }),
                        })),
                        LEFT_ASSOC => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| {
                                    if args.len() < 2 {
                                        return None;
                                    };
                                    let first = args[0].to_intrinsic();
                                    let IntrinsicSort::BitVec(first_sz) = first else {
                                        return None;
                                    };
                                    for another in &args[1..] {
                                        let second = another.to_intrinsic();
                                        let IntrinsicSort::BitVec(another_sz) = second else {
                                            return None;
                                        };
                                        if first_sz != another_sz {
                                            return None;
                                        }
                                    }
                                    return Some(args[0].clone());
                                }),
                            }))
                        },
                        COMPARE_PREDICATE => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [first, second] => {
                                        let first = first.to_intrinsic();
                                        let second = second.to_intrinsic();
                                        match (first, second) {
                                            (IntrinsicSort::BitVec(i), IntrinsicSort::BitVec(j)) => {
                                                if i == j {
                                                    Some(IntrinsicSort::Bool.into())
                                                } else {
                                                    None
                                                }
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "bvcomp" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [first, second] => {
                                        let first = first.to_intrinsic();
                                        let second = second.to_intrinsic();
                                        match (first, second) {
                                            (IntrinsicSort::BitVec(i), IntrinsicSort::BitVec(j)) => {
                                                if i == j {
                                                    Some(IntrinsicSort::BitVec(1).into())
                                                } else {
                                                    None
                                                }
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "bv2bool" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [arg] => {
                                        let arg = arg.to_intrinsic();
                                        match arg {
                                            IntrinsicSort::BitVec(1) => Some(bool_sort()),
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "bool2bv" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [arg] => {
                                        if arg.is_bool() {
                                            Some(bv_sort(1))
                                        } else {
                                            None
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "concat" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| match args {
                                    [first, second] => {
                                        let first = first.to_intrinsic();
                                        let second = second.to_intrinsic();
                                        match (first, second) {
                                            (IntrinsicSort::BitVec(i), IntrinsicSort::BitVec(j)) => {
                                                Some(IntrinsicSort::BitVec(i + j).into())
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        },
                        "bvxor" => {
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(|args| {
                                    if args.len() < 2 {
                                        return None;
                                    };
                                    let first = args[0].to_intrinsic();
                                    let IntrinsicSort::BitVec(first_sz) = first else {
                                        return None;
                                    };
                                    for another in &args[1..] {
                                        let second = another.to_intrinsic();
                                        let IntrinsicSort::BitVec(another_sz) = second else {
                                            return None;
                                        };
                                        if first_sz != another_sz {
                                            return None;
                                        }
                                    }
                                    return Some(args[0].clone());
                                }),
                            }))
                        },
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    }
                }
            }
            KRPKIdentifier::Indexed(name, indices) => {
                match name.as_str() {
                    "extract" => {
                        match indices.as_slice() {
                            [KRPKIndex::Numeral(i), KRPKIndex::Numeral(j)] => {
                                let i = *i;
                                let j = *j;
                                Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                    id: func_id.clone(),
                                    sort_mapping: Rc::new(move |args| {
                                        match args {
                                            [first] => {
                                                let first = first.to_intrinsic();
                                                match first {
                                                    IntrinsicSort::BitVec(_m) => {
                                                        // XXX: Whether need to check the range from i to j compared to _m?
                                                        Some(
                                                            IntrinsicSort::BitVec(i - j + 1).into(),
                                                        )
                                                    }
                                                    _ => None,
                                                }
                                            }
                                            _ => None,
                                        }
                                    }),
                                }))
                            }
                            _ => Err(FunctionError::Undefined(func_id.clone())),
                        }
                    }
                    "repeat" => match indices.as_slice() {
                        [KRPKIndex::Numeral(i)] => {
                            if *i == 0 {
                                Err(FunctionError::Undefined(func_id.clone()))
                            } else {
                                let i = *i;
                                Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                    id: func_id.clone(),
                                    sort_mapping: Rc::new(move |args| match args {
                                        [first] => {
                                            let first = first.to_intrinsic();
                                            match first {
                                                IntrinsicSort::BitVec(_m) => {
                                                    Some(IntrinsicSort::BitVec(_m * i).into())
                                                }
                                                _ => None,
                                            }
                                        }
                                        _ => None,
                                    }),
                                }))
                            }
                        }
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    },
                    "zero_extend" => match indices.as_slice() {
                        [KRPKIndex::Numeral(i)] => {
                            let i = *i;
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(move |args| match args {
                                    [first] => {
                                        let first = first.to_intrinsic();
                                        match first {
                                            IntrinsicSort::BitVec(m) => {
                                                Some(IntrinsicSort::BitVec(m + i).into())
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        }
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    },
                    "sign_extend" => match indices.as_slice() {
                        [KRPKIndex::Numeral(i)] => {
                            let i = *i;
                            Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                                id: func_id.clone(),
                                sort_mapping: Rc::new(move |args| match args {
                                    [first] => {
                                        let first = first.to_intrinsic();
                                        match first {
                                            IntrinsicSort::BitVec(m) => {
                                                Some(IntrinsicSort::BitVec(m + i).into())
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                }),
                            }))
                        }
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    },
                    "rotate_left" => match indices.as_slice() {
                        [_i] => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                            id: func_id.clone(),
                            sort_mapping: Rc::new(|args| match args {
                                [first] => {
                                    let first = first.to_intrinsic();
                                    match first {
                                        IntrinsicSort::BitVec(m) => {
                                            Some(IntrinsicSort::BitVec(m).into())
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }),
                        })),
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    },
                    "rotate_right" => match indices.as_slice() {
                        [_i] => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                            id: func_id.clone(),
                            sort_mapping: Rc::new(|args| match args {
                                [first] => {
                                    let first = first.to_intrinsic();
                                    match first {
                                        IntrinsicSort::BitVec(m) => {
                                            Some(IntrinsicSort::BitVec(m).into())
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }),
                        })),
                        _ => Err(FunctionError::Undefined(func_id.clone())),
                    },
                    _ => Err(FunctionError::Undefined(func_id.clone())),
                }
            }
        }
    }

    fn arrays_ex_function(&self, func_id: &KRPKIdentifier) -> Result<KRPKFunction, FunctionError> {
        match func_id {
            KRPKIdentifier::Symbol(sym) => match sym.as_str() {
                "select" => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                    id: func_id.clone(),
                    sort_mapping: Rc::new(|args| match args {
                        [first, second] => {
                            let first = first.to_intrinsic();
                            let second = second.to_intrinsic();
                            match (first, second) {
                                (IntrinsicSort::Array(domain, range), index) => {
                                    if *domain == index {
                                        Some((*range).into())
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }),
                })),
                "store" => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                    id: func_id.clone(),
                    sort_mapping: Rc::new(|args| match args {
                        [first, second, third] => {
                            let first = first.to_intrinsic();
                            let second = second.to_intrinsic();
                            let third = third.to_intrinsic();
                            match (&first, &second, &third) {
                                (IntrinsicSort::Array(domain, range), index, value) => {
                                    if **domain == *index && **range == *value {
                                        Some(first.into())
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }),
                })),
                // Z3's const arrays in the form of `((as const (Array D R)) const_value)`
                "const" => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                    id: func_id.clone(),
                    sort_mapping: Rc::new(|arg_and_coercion_sort| match arg_and_coercion_sort {
                        [arg_sort, coercion_sort] => {
                            let IntrinsicSort::Array(_domain, range) = coercion_sort.to_intrinsic()
                            else {
                                return None;
                            };
                            if arg_sort.to_intrinsic() != *range {
                                None
                            } else {
                                Some(coercion_sort.clone())
                            }
                        }
                        _ => None,
                    }),
                })),
                "ensure_index" => Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                    id: func_id.clone(),
                    sort_mapping: Rc::new(|args| match args {
                        [first, second] => {
                            let first = first.to_intrinsic();
                            let second = second.to_intrinsic();
                            match (first, second) {
                                (IntrinsicSort::Array(domain, _range), index) => {
                                    match (*domain, index) {
                                        (IntrinsicSort::BitVec(i), IntrinsicSort::BitVec(j)) => {
                                            if i == j {
                                                Some(IntrinsicSort::Bool.into())
                                            } else {
                                                None
                                            }
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }),
                })),
                _ => Err(FunctionError::Undefined(func_id.clone())),
            },
            KRPKIdentifier::Indexed(sym, indices) => match sym.as_str() {
                // XXX: An ugly workaround to avoid stack overflow when parsing too large const array expressions.
                "god_save_me_const" => match indices.as_slice() {
                    [KRPKIndex::Symbol(bytes)] => {
                        debug_assert!(bytes.chars().all(|c| c.is_ascii_hexdigit()));
                        Ok(KRPKFunction::Predefined(KRPKFunctionDeclaration {
                            id: func_id.clone(),
                            sort_mapping: Rc::new(|arg_and_coercion_sort| match arg_and_coercion_sort {
                                [arg_sort, coercion_sort] => {
                                    let IntrinsicSort::Array(_domain, range) = coercion_sort.to_intrinsic()
                                    else {
                                        return None;
                                    };
                                    if arg_sort.to_intrinsic() != *range {
                                        None
                                    } else {
                                        Some(coercion_sort.clone())
                                    }
                                }
                                _ => None,
                            }),
                        }))
                    }
                    _ => Err(FunctionError::Undefined(func_id.clone())),
                }
                _ => Err(FunctionError::Undefined(func_id.clone())),
            }
            // _ => Err(FunctionError::Undefined(func_id.clone())),
        }
    }
}
