use std::ffi::{c_char, CStr};
use std::sync::Arc;
use itertools::Itertools;
use hir::{Identifier, Index, QualIdentifier, Symbol, Term, MemoryCell, StringLiteral};
use crate::hir::Command;

fn __rc_helper<T: ?Sized>(ptr: *const T) -> Arc<T> {
    let tmp = unsafe { Arc::from_raw(ptr) };
    let r = tmp.clone();
    std::mem::forget(tmp);
    r
}

pub type KFuzzSolver = FuzzSolver;
pub type KSolution = fuzzend::Solution;
pub type KModel = fuzzend::response::Model;

/// An array of [`KASTNode`]s with elements arranged in sequence. It is required since sometimes we need to receive an array
/// of AST nodes from C side and C arrays must have a consequent memory layout.
/// 
/// This is an auxiliary data structure and should be hidden by higher-level language (e.g., C++) APIs by using [`krpk_make_ast_array`].
#[repr(C)]
pub struct KASTArray {
    pub len: u64,
    pub data: *const Arc<KASTNode>,
}

impl KASTArray {
    pub fn from_vec(vec: Vec<Arc<KASTNode>>) -> Self {
        let mut vec = vec;
        let len = vec.len() as u64;
        let data = if len == 0 {
            return Self::empty();
        } else {
            vec.shrink_to_fit();
            let r = vec.as_ptr();
            std::mem::forget(vec);
            r
        };
        KASTArray { len, data }
    }

    pub fn empty() -> Self {
        KASTArray {
            len: 0,
            data: std::ptr::null(),
        }
    }

    pub fn to_vec(&self) -> Vec<Arc<KASTNode>> {
        unsafe {
            Vec::from_raw_parts(
                self.data as *mut Arc<KASTNode>,
                self.len as usize,
                self.len as usize,
            )
        }
    }
}

/// An [`KASTNode`] is a node corresponding to one of the ASTs in [`crate::hir`]. It is the C counterpart
/// of [`InnerASTNode`] who is semantically equivalent to [`KASTNode`] but cannot be appropriately handled by C.
/// (Approximately, consider an [`KASTNode`] as a raw pointer to an [`InnerASTObject`].)
/// 
/// This struct records two pieces of information: the children of the node, and
/// a constructor that takes the children and returns the corresponding AST.
/// The constructor is a function pointer with the type `fn(Vec<InnerASTNode>) -> HIRObject`, where
/// [`HIRObject`] wraps different HIR ASTs.
/// 
/// Extra information to construct the AST is stored in the constructor (which is typically a closure).
/// 
/// To use this struct, you should convert it to an [`InnerASTNode`] by [`KASTNode::to_object`].
/// 
/// ```
/// # let inner_node = InnerASTNode {
/// #   children: vec![],
/// #   construct: Arc::new(move |children| {
/// #       HIRObject::Symbol(Located::no_loc(Symbol::Simple("true".to_string())))
/// #   }),
/// # };
/// # let ast_node_used_by_c = inner_node.into_raw();
/// let ast_node_used_by_rust = ast_node_used_by_c.to_object();
/// ```
#[repr(C)]
pub struct KASTNode {
    children: KASTArray,
    construct: *const ObjectConstructor,
}

type ObjectConstructor = dyn Fn(Vec<InnerASTNode>) -> HIRObject;

impl Drop for KASTNode {
    fn drop(&mut self) {
        let _construct = unsafe { Arc::from_raw(self.construct) };
        let _children = self.children.to_vec();
    }
}

impl KASTNode {
    /// Convert an [`KASTNode`] to an [`InnerASTObject`] which is easier to be handled by Rust.
    fn to_object(&self) -> InnerASTNode {
        let children = {
            let tmp = self.children.to_vec();
            let r = tmp.iter().map(|node| node.to_object()).collect_vec();
            std::mem::forget(tmp);
            r
        };
        let construct = __rc_helper(self.construct);
        InnerASTNode {
            children,
            construct,
        }
    }
}

/// Wrapper of different HIR ASTs.
#[derive(Debug, Clone, PartialEq)]
enum HIRObject {
    Term(Term),
    QualIdentifier(QualIdentifier),
    Symbol(Symbol),
    Index(Index),
    SMTScript(SMTScript),
    Sort(Sort),
    Identifier(Identifier),
    SpecConstant(SpecConstant),
    Attribute(Attribute),
    Command(Command),
}

/// An AST node corresponds to one of the ASTs in [`crate::hir`].
/// This struct records two pieces of information: the children of the node, and
/// a constructor that takes the children and returns the corresponding AST.
/// The constructor is a function pointer with the type `fn(Vec<InnerASTNode>) -> HIRObject`, where
/// [`HIRObject`] wraps different HIR ASTs.
///
/// Extra information to construct the AST is stored in the constructor (which is typically a closure).
/// 
/// Typically, an [`InnerASTNode`] is constructed thus:
/// ```
/// let ast_node = InnerASTNode {
///   children: vec![],
///   construct: Arc::new(move |children| {
///       HIRObject::Symbol(Located::no_loc(Symbol::Simple("true".to_string())))
///   }),
/// };
/// ```
/// and used thus:
/// ```
/// let ast = ast_node.construct();
/// ```
struct InnerASTNode {
    children: Vec<InnerASTNode>,
    construct: Arc<ObjectConstructor>,
}

impl InnerASTNode {
    fn construct(self) -> HIRObject {
        (self.construct)(self.children)
    }

    fn into_raw(self) -> Arc<KASTNode> {
        let InnerASTNode {
            children,
            construct,
        } = self;
        let raw_children = children.into_iter().map(|obj| obj.into_raw()).collect_vec();
        let _len = raw_children.len() as u64;
        let children = { KASTArray::from_vec(raw_children) };
        let construct = Arc::into_raw(construct) as *const _;
        Arc::new(KASTNode {
            children,
            construct,
        })
    }
}

/// An auxiliary API to re-arrange AST nodes in `KASTNode **[]` to an array with a consequent layout by the following mapping
/// ```text
/// KASTNode** ptr -> **ptr
/// ```
/// 
/// Elements are second-level pointers of [`KASTNode`] since return values of other APIs are first-order pointers, and we cannot directly
/// move them to the array memory and can only copy pointers to these pointers into the array.
#[no_mangle]
pub extern "C" fn krpk_make_ast_array(asts: *const *const *const KASTNode, len: u64) -> KASTArray {
    if len == 0 {
        assert!(asts.is_null());
        return KASTArray::empty();
    }
    let asts = unsafe {
        let tmp = std::slice::from_raw_parts(asts, len as usize);
        let mut r = Vec::with_capacity(tmp.len());
        for ptr in tmp.iter() {
            let tt = **ptr;
            r.push(__rc_helper(tt));
        }
        r
    };
    KASTArray::from_vec(asts)
}

/// Make the term `true`.
#[no_mangle]
pub extern "C" fn krpk_make_true() -> *const KASTNode {
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            let term =
                Term::QualIdentifier(QualIdentifier::Simple(
                    Identifier::Symbol(Symbol::Simple("true".to_string())),
                ));
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_true`].
#[no_mangle]
pub extern "C" fn krpk_make_false() -> *const KASTNode {
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            let term =
                Term::QualIdentifier(QualIdentifier::Simple(
                    Identifier::Symbol(Symbol::Simple("false".to_string())),
                ));
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Clone ref-count pointers to AST nodes. Needed when the C structs are copied.
#[no_mangle]
pub extern "C" fn krpk_ast_node_clone(node: *const KASTNode) -> *const KASTNode {
    Arc::into_raw(__rc_helper(node))
}

/// Make the term `(some_func arg1 arg2 arg3...)`
#[no_mangle]
pub extern "C" fn krpk_make_apply(func: *const KASTNode, args: KASTArray) -> *const KASTNode {
    let mut children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    children.push({
        let tmp = unsafe { Arc::from_raw(func) };
        let r = tmp.to_object();
        std::mem::forget(tmp);
        r
    });
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let func = children.pop().unwrap();

            let func = if let HIRObject::QualIdentifier(qid) = func.construct() {
                qid
            } else {
                panic!("Expected QualIdentifier")
            };

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make the identifier with a bald symbol `symbol` (when there's no indices) or the identifier 
/// `(_ symbol index1 index2...)` (when there are indices).
#[no_mangle]
pub extern "C" fn krpk_make_identifier(
    symbol: *const KASTNode,
    indices: KASTArray,
) -> *const KASTNode {
    let index_count = indices.len;
    let r = if index_count == 0 {
        let children = vec![{
            let tmp = __rc_helper(symbol);
            let r = tmp.to_object();
            // std::mem::forget(tmp);
            r
        }];
        let result = InnerASTNode {
            children,
            construct: Arc::new(move |children: Vec<InnerASTNode>| {
                let mut children = children;
                let symbol = children.pop().unwrap();
                assert!(children.is_empty());
                let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                    symbol
                } else {
                    panic!("Expected Symbol")
                };
                let identifier = Identifier::Symbol(symbol);
                HIRObject::Identifier(identifier)
            }),
        };
        result.into_raw()
    } else {
        let mut children = {
            let tmp = indices.to_vec();
            let r = tmp.clone();
            r
        };
        children.push(__rc_helper(symbol));
        let result = InnerASTNode {
            children: children.iter().map(|node| node.to_object()).collect_vec(),
            construct: Arc::new(move |children: Vec<InnerASTNode>| {
                let mut children = children;
                let symbol = children.pop().unwrap();
                let mut indices = vec![];
                for index in children {
                    indices.push(if let HIRObject::Index(index) = index.construct() {
                        index
                    } else {
                        panic!("Expected Term")
                    });
                }
                let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                    symbol
                } else {
                    panic!("Expected Symbol")
                };
                let identifier = Identifier::Indexed(symbol, indices);
                HIRObject::Identifier(identifier)
            }),
        };
        // std::mem::forget(children);
        result.into_raw()
    };
    // std::mem::forget(indices);
    Arc::into_raw(r)
}

/// Make a ground sort whose identifier is `id`.
/// A ground sort is a sort without generic parameters.
/// For example, `Int` and `(_ BitVec 32)` (`32` is an index, not a generic arg).
#[no_mangle]
pub extern "C" fn krpk_make_simple_sort(id: *const KASTNode) -> *const KASTNode {
    let id = __rc_helper(id).to_object();
    let result = InnerASTNode {
        children: vec![id],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(1, children.len());
            let id = children.pop().unwrap();
            let id = if let HIRObject::Identifier(id) = id.construct() {
                id
            } else {
                panic!("Expected Identifier")
            };
            let sort = Sort::Simple(id);
            HIRObject::Sort(sort)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a parametric sort with generic parameters reified to `sort_args`.
/// For example,
/// ```text
/// (Array Int Int)
/// ```
/// Here, the `Int`s are the `sort_args`.
#[no_mangle]
pub extern "C" fn krpk_make_parametric_sort(
    id: *const KASTNode,
    sort_args: KASTArray,
) -> *const KASTNode {
    let id = __rc_helper(id).to_object();
    let mut children = {
        let tmp = sort_args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        r
    };
    children.push(id);
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let id = if let HIRObject::Identifier(id) = children.pop().unwrap().construct() {
                id
            } else {
                panic!("Expected Identifier")
            };
            assert!(!children.is_empty());
            let mut sort_args = vec![];
            for sort_arg in children {
                sort_args.push(if let HIRObject::Sort(sort_arg) = sort_arg.construct() {
                    sort_arg
                } else {
                    panic!("Expected Sort")
                });
            }
            let sort = Sort::Parametric(id, sort_args);
            HIRObject::Sort(sort)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Wrap a qual id into an atomic term. Atomic term is the most elementary blocks that can appear in a term.
/// Such qual ids are constructed by `krpk_make_qual_identifier`.
#[no_mangle]
pub extern "C" fn krpk_make_atom(qual_identifier: *const KASTNode) -> *const KASTNode {
    let id = __rc_helper(qual_identifier).to_object();
    let result = InnerASTNode {
        children: vec![id],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(1, children.len());
            let id = children.pop().unwrap();
            let id = if let HIRObject::QualIdentifier(id) = id.construct() {
                id
            } else {
                panic!("Expected Identifier")
            };
            let term = Term::QualIdentifier(id);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a qual id with or *without* a sort qualifier. For example, `(as const (Array Int Int))` is a qual id with a sort qualifier
/// where `const` is the bald id and `(Array Int Int)` is the sort qualifier, and `bvand` is a qual id without a sort qualifier.
#[no_mangle]
pub extern "C" fn krpk_make_qual_identifier(
    symbol: *const KASTNode,
    indices: KASTArray,
    sort: *const KASTNode,
) -> *const KASTNode {
    let index_count = indices.len;
    let qualified = !sort.is_null();
    let r = if index_count == 0 {
        let children = if qualified {
            vec![
                {
                    let tmp = __rc_helper(sort);
                    let r = tmp.to_object();
                    r
                },
                {
                    let tmp = __rc_helper(symbol);
                    let r = tmp.to_object();
                    r
                },
            ]
        } else {
            vec![{
                let tmp = __rc_helper(symbol);
                let r = tmp.to_object();
                r
            }]
        };
        let result = InnerASTNode {
            children,
            construct: Arc::new(move |children: Vec<InnerASTNode>| {
                let mut children = children;
                if qualified {
                    assert_eq!(2, children.len());
                    let symbol = children.pop().unwrap();
                    let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                        symbol
                    } else {
                        panic!("Expected Symbol")
                    };
                    let sort = children.pop().unwrap();
                    let sort = if let HIRObject::Sort(sort) = sort.construct() {
                        sort
                    } else {
                        panic!("Expected Sort")
                    };
                    let identifier = Identifier::Symbol(symbol);
                    let qual_identifier =
                        QualIdentifier::Qualified(identifier, sort);
                    HIRObject::QualIdentifier(qual_identifier)
                } else {
                    assert_eq!(1, children.len());
                    let symbol = children.pop().unwrap();
                    let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                        symbol
                    } else {
                        panic!("Expected Symbol")
                    };
                    let identifier = Identifier::Symbol(symbol);
                    let qual_identifier = QualIdentifier::Simple(identifier);
                    HIRObject::QualIdentifier(qual_identifier)
                }
            }),
        };
        result.into_raw()
    } else {
        let mut children = {
            let tmp = indices.to_vec();
            let r = tmp.clone();
            r
        };
        if qualified {
            children.push(unsafe { Arc::from_raw(sort) });
        }
        children.push(unsafe { Arc::from_raw(symbol) });
        let result = InnerASTNode {
            children: children.iter().map(|node| node.to_object()).collect_vec(),
            construct: Arc::new(move |children: Vec<InnerASTNode>| {
                let mut children = children;
                if qualified {
                    let symbol = children.pop().unwrap();
                    let sort = children.pop().unwrap();
                    let mut indices = vec![];
                    for index in children {
                        indices.push(if let HIRObject::Index(index) = index.construct() {
                            index
                        } else {
                            panic!("Expected Term")
                        });
                    }
                    let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                        symbol
                    } else {
                        panic!("Expected Symbol")
                    };
                    let sort = if let HIRObject::Sort(sort) = sort.construct() {
                        sort
                    } else {
                        panic!("Expected Sort")
                    };
                    let identifier = Identifier::Indexed(symbol, indices);
                    let qual_identifier =
                        QualIdentifier::Qualified(identifier, sort);
                    HIRObject::QualIdentifier(qual_identifier)
                } else {
                    let symbol = children.pop().unwrap();
                    let mut indices = vec![];
                    for index in children {
                        indices.push(if let HIRObject::Index(index) = index.construct() {
                            index
                        } else {
                            panic!("Expected Term")
                        });
                    }
                    let symbol = if let HIRObject::Symbol(symbol) = symbol.construct() {
                        symbol
                    } else {
                        panic!("Expected Symbol")
                    };
                    let identifier = Identifier::Indexed(symbol, indices);
                    let qual_identifier = QualIdentifier::Simple(identifier);
                    HIRObject::QualIdentifier(qual_identifier)
                }
            }),
        };
        std::mem::forget(children);
        result.into_raw()
    };
    Arc::into_raw(r)
}

/// Make a symbol `str`.
#[no_mangle]
pub extern "C" fn krpk_make_simple_symbol(str: *const c_char) -> *const KASTNode {
    let symbol_name = unsafe { CStr::from_ptr(str) }
        .to_owned()
        .into_string()
        .unwrap();
    let symbol = Symbol::Simple(symbol_name);
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            HIRObject::Symbol(symbol.clone())
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a quoted symbol `|str|`.
#[no_mangle]
pub extern "C" fn krpk_make_quoted_symbol(str: *const c_char) -> *const KASTNode {
    let symbol_name = unsafe { CStr::from_ptr(str) }
        .to_owned()
        .into_string()
        .unwrap();
    let symbol = Symbol::Quoted(symbol_name);
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            HIRObject::Symbol(symbol.clone())
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Destruct an AST node. Should be hidden behind high-level APIs.
#[no_mangle]
pub extern "C" fn krpk_drop_ast_node(ast_node: *const KASTNode) {
    let _to_drop = unsafe { Arc::from_raw(ast_node) };
}

/// Construct a fuzz solver.
#[no_mangle]
pub extern "C" fn krpk_make_fuzz_solver() -> *mut FuzzSolver {
    let solver = FuzzSolver::new();
    Box::into_raw(Box::new(solver))
}

#[no_mangle]
pub extern "C" fn krpk_fuzz_solver_set_option(
    solver: *mut FuzzSolver,
    option: *const c_char,
    value: *const c_char,
) {
    let mut solver = unsafe { Box::from_raw(solver) };
    let option = unsafe { CStr::from_ptr(option) }
        .to_owned()
        .into_string()
        .unwrap();
    let value = unsafe { CStr::from_ptr(value) }
        .to_owned()
        .into_string()
        .unwrap();
    solver.set_fuzzer_option(&option, &value);
    std::mem::forget(solver);
}

/// Destruct a fuzz solver. Should be hidden behind high-level APIs.
#[no_mangle]
pub extern "C" fn krpk_drop_fuzz_solver(fuzz_solver: *const KFuzzSolver) {
    let _to_drop = unsafe { Box::from_raw(fuzz_solver as *mut KFuzzSolver) };
}

/// Solve an SMT-LIB 2 scripts.
#[no_mangle]
pub extern "C" fn krpk_solver_solve(
    solver: *mut FuzzSolver,
    smt_script: *const KASTNode,
) -> *const KSolution {
    let mut solver = unsafe { Box::from_raw(solver) };
    let smt_script = if let HIRObject::SMTScript(script) = {
        let tmp = __rc_helper(smt_script);
        tmp.to_object().construct()
    } {
        script
    } else {
        panic!("Expected SMTScript")
    };
    let solution = solver.solve(&smt_script).unwrap();
    std::mem::forget(solver);
    Box::into_raw(Box::new(solution))
}

/// Destruct a solution. Should be hidden behind high-level APIs.
#[no_mangle]
pub extern "C" fn krpk_drop_solution(solution: *const KSolution) {
    let _to_drop = unsafe { Box::from_raw(solution as *mut KSolution) };
}

/// Whether the solution is a SAT?
#[no_mangle]
pub extern "C" fn krpk_solution_is_sat(solution: *const KSolution) -> bool {
    let solution = unsafe { Box::from_raw(solution as *mut KSolution) };
    let is_sat = if let Solution::Sat(..) = *solution {
        true
    } else {
        false
    };
    std::mem::forget(solution);
    is_sat
}

/// Whether the solution is an UNKNOWN?
#[no_mangle]
pub extern "C" fn krpk_solution_is_unknown(solution: *const KSolution) -> bool {
    let solution = unsafe { Box::from_raw(solution as *mut KSolution) };
    let is_sat = if let Solution::Unknown = *solution {
        true
    } else {
        false
    };
    std::mem::forget(solution);
    is_sat
}

/// Get the solution model when the solution is SAT.
#[no_mangle]
pub extern "C" fn krpk_solution_get_model(solution: *const KSolution) -> *const KModel {
    let solution = unsafe { Box::from_raw(solution as *mut KSolution) };
    let model = if let Solution::Sat(ref model) = *solution {
        model as *const _
    } else {
        panic!("Solution is not sat")
    };
    std::mem::forget(solution);
    model
}

/// Anonymous struct for bit vector literals. Should be hidden behind high-level APIs.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct __KBitVecData {
    pub width_in_bits: u64,
    pub data: *const u8,
}

/// Anonymous struct for key-value pairs (both the key and the value are bytes). Should be hidden behind high-level APIs.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct __KIndexValuePair {
    pub index: *const u8,
    pub value: *const u8,
}

/// Anonymous struct for bit vec array literals. Should be hidden behind high-level APIs.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct __KBVArrayData {
    pub index_width_in_bits: u64,
    pub value_width_in_bits: u64,
    pub len: u64,
    pub index_value_pairs: *const __KIndexValuePair,
}

/// Anonymous union for different kinds of literals. Should be hidden behind high-level APIs.
/// It can be a boolean value, a bit vec, or a bit vec array.
#[repr(C)]
#[derive(Copy, Clone)]
pub union __KLiteralData {
    pub bitvec: __KBitVecData,
    pub boolean: bool,
    pub bv_array: __KBVArrayData,
}

///Struct for literals assigned to unknowns in the solution returned by the fuzz solver. It consists of a kind flag
/// with 0 corresponding to `Bool`, 1 corresponding to `BitVec`, and 2 corresponding to `BitVecArray`, and a union holds
/// the actual data.
#[repr(C)]
#[derive(Copy, Clone)]
pub struct KLiteral {
    kind: u8,
    data: __KLiteralData,
}

/// Destruct a literal. Should be hidden behind high-level APIs.
#[no_mangle]
pub extern "C" fn krpk_drop_literal(literal: KLiteral) {
    match literal.kind {
        1 => {
            let _to_drop = unsafe { Box::from_raw(literal.data.bitvec.data as *mut u8) };
        }
        2 => {
            let pairs = unsafe {
                Vec::from_raw_parts(
                    literal.data.bv_array.index_value_pairs as *mut __KIndexValuePair,
                    literal.data.bv_array.len as usize,
                    literal.data.bv_array.len as usize,
                )
            };
            let index_width_in_bytes = unsafe {
                literal.data.bv_array.index_width_in_bits / 8
                    + if literal.data.bv_array.index_width_in_bits % 8 == 0 {
                        0
                    } else {
                        1
                    }
            };
            let value_width_in_bytes = unsafe {
                literal.data.bv_array.value_width_in_bits / 8
                    + if literal.data.bv_array.value_width_in_bits % 8 == 0 {
                        0
                    } else {
                        1
                    }
            };
            for p in pairs {
                let _index = unsafe {
                    Vec::from_raw_parts(
                        p.index as *mut u8,
                        index_width_in_bytes as usize,
                        index_width_in_bytes as usize,
                    )
                };
                let _value = unsafe {
                    Vec::from_raw_parts(
                        p.value as *mut u8,
                        value_width_in_bytes as usize,
                        value_width_in_bytes as usize,
                    )
                };
            }
        }
        _ => (),
    }
}

#[no_mangle]
pub extern "C" fn krpk_model_contains_value_of(
    model: *const KModel,
    constant_name: *const c_char,
) -> bool {
    let model = unsafe { Box::from_raw(model as *mut KModel) };
    let constant_name = unsafe {
        CStr::from_ptr(constant_name)
            .to_owned()
            .into_string()
            .unwrap()
    };
    let r = model.contains_unknown_by_name(&constant_name);
    std::mem::forget(model);
    r
}

#[no_mangle]
pub extern "C" fn krpk_default_bv_array_literal(
    domain: u64,
    range: u64,
    size: u64,
) -> KLiteral {
    let mut pairs = vec![];
    for index in 0..size {
        let index = {
            let mut tmp = vec![];
            match domain {
                8 => {
                    let idx_tmp = index as u32;
                    tmp.push((idx_tmp & 0xFF) as u8);
                }
                16 => {
                    let idx_tmp = index as u32;
                    tmp.push((idx_tmp & 0xFF) as u8);
                    tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                }
                32 => {
                    let idx_tmp = index as u32;
                    tmp.push((idx_tmp & 0xFF) as u8);
                    tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                    tmp.push(((idx_tmp & 0xFF0000) >> 16) as u8);
                    tmp.push(((idx_tmp & 0xFF000000) >> 24) as u8);
                }
                64 => {
                    let idx_tmp = index as u64;
                    tmp.push((idx_tmp & 0xFF) as u8);
                    tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                    tmp.push(((idx_tmp & 0xFF0000) >> 16) as u8);
                    tmp.push(((idx_tmp & 0xFF000000) >> 24) as u8);
                    tmp.push(((idx_tmp & 0xFF00000000) >> 32) as u8);
                    tmp.push(((idx_tmp & 0xFF0000000000) >> 40) as u8);
                    tmp.push(((idx_tmp & 0xFF000000000000) >> 48) as u8);
                    tmp.push(((idx_tmp & 0xFF00000000000000) >> 56) as u8);
                }
                _ => unimplemented!(),
            }
            tmp.shrink_to_fit();
            let r = tmp.as_ptr();
            std::mem::forget(tmp);
            r
        };
        let value = {
            let mut tmp = vec![0; ((range + 7) / 8) as usize];
            tmp.shrink_to_fit();
            let r = tmp.as_ptr();
            std::mem::forget(tmp);
            r
        };
        pairs.push(__KIndexValuePair { index, value });
    }
    let bv_array = __KBVArrayData {
        index_width_in_bits: domain,
        value_width_in_bits: range,
        len: size,
        index_value_pairs: {
            let mut tmp = pairs.clone();
            tmp.shrink_to_fit();
            let r = tmp.as_ptr();
            std::mem::forget(tmp);
            r
        },
    };
    let ld = __KLiteralData { bv_array };
    KLiteral { kind: 2, data: ld }
}

/// Get the value assigned to an unknown with name `constant_name` provided by the model in a solution
/// returned by the fuzz solver.
#[no_mangle]
pub extern "C" fn krpk_model_get_value(
    model: *const KModel,
    constant_name: *const c_char,
) -> KLiteral {
    let model = unsafe { Box::from_raw(model as *mut KModel) };
    let constant_name = unsafe {
        CStr::from_ptr(constant_name)
            .to_owned()
            .into_string()
            .unwrap()
    };
    let Some(solution) = model.value_by_name(&constant_name) else {
        panic!("Unknown constant: {}", &constant_name)
    };
    let r = match solution {
        mir::LiteralValue::BitVecValue(width_in_bits, bytes) => {
            let bv = __KBitVecData {
                width_in_bits: *width_in_bits as u64,
                data: {
                    let mut tmp = bytes.clone();
                    tmp.shrink_to_fit();
                    let r = tmp.as_ptr();
                    std::mem::forget(tmp);
                    r
                },
            };
            let ld = __KLiteralData { bitvec: bv };
            KLiteral { kind: 1, data: ld }
        }
        mir::LiteralValue::BitVecArrayValue(index_width_in_bits, value_width_in_bits, data) => {
            let mut pairs = vec![];
            for (index, value) in data.iter().enumerate() {
                let index = {
                    let mut tmp = vec![];
                    match *index_width_in_bits {
                        8 => {
                            let idx_tmp = index as u32;
                            tmp.push((idx_tmp & 0xFF) as u8);
                        }
                        16 => {
                            let idx_tmp = index as u32;
                            tmp.push((idx_tmp & 0xFF) as u8);
                            tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                        }
                        32 => {
                            let idx_tmp = index as u32;
                            tmp.push((idx_tmp & 0xFF) as u8);
                            tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                            tmp.push(((idx_tmp & 0xFF0000) >> 16) as u8);
                            tmp.push(((idx_tmp & 0xFF000000) >> 24) as u8);
                        }
                        64 => {
                            let idx_tmp = index as u64;
                            tmp.push((idx_tmp & 0xFF) as u8);
                            tmp.push(((idx_tmp & 0xFF00) >> 8) as u8);
                            tmp.push(((idx_tmp & 0xFF0000) >> 16) as u8);
                            tmp.push(((idx_tmp & 0xFF000000) >> 24) as u8);
                            tmp.push(((idx_tmp & 0xFF00000000) >> 32) as u8);
                            tmp.push(((idx_tmp & 0xFF0000000000) >> 40) as u8);
                            tmp.push(((idx_tmp & 0xFF000000000000) >> 48) as u8);
                            tmp.push(((idx_tmp & 0xFF00000000000000) >> 56) as u8);
                        }
                        _ => unimplemented!(),
                    }
                    tmp.shrink_to_fit();
                    let r = tmp.as_ptr();
                    std::mem::forget(tmp);
                    r
                };
                let value = {
                    let mut tmp = value.clone();
                    tmp.shrink_to_fit();
                    let r = tmp.as_ptr();
                    std::mem::forget(tmp);
                    r
                };
                pairs.push(__KIndexValuePair { index, value });
            }
            let bv_array = __KBVArrayData {
                index_width_in_bits: *index_width_in_bits as u64,
                value_width_in_bits: *value_width_in_bits as u64,
                len: pairs.len() as u64,
                index_value_pairs: {
                    let mut tmp = pairs.clone();
                    tmp.shrink_to_fit();
                    let r = tmp.as_ptr();
                    std::mem::forget(tmp);
                    r
                },
            };
            let ld = __KLiteralData { bv_array };
            KLiteral { kind: 2, data: ld }
        }
        mir::LiteralValue::BoolValue(bv) => KLiteral {
            kind: 0,
            data: __KLiteralData { boolean: *bv },
        },
    };
    std::mem::forget(model);
    r
}

/// Make a numeral index.
#[no_mangle]
pub extern "C" fn krpk_make_numeral_index(numeral: usize) -> *const KASTNode {
    let index = Index::Numeral(Numeral(numeral));
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            HIRObject::Index(index.clone())
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a symbol index where the symbol is `str`.
#[no_mangle]
pub extern "C" fn krpk_make_symbol_index(str: *const c_char) -> *const KASTNode {
    let symbol_name = unsafe { CStr::from_ptr(str) }
        .to_owned()
        .into_string()
        .unwrap();
    let symbol = Index::Symbol(Symbol::Simple(symbol_name));
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            HIRObject::Index(symbol.clone())
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a spec constant that wraps a numeral (`123456`), hexadecimal (`#x7FFA`), binary (`#b010001`), string (`"SPY x FAMILY"`),
/// or decimal (`114.514`).
#[no_mangle]
pub extern "C" fn krpk_make_spec_constant(node: *const KASTNode) -> *const KASTNode {
    let children = vec![{
        let tmp = __rc_helper(node);
        let r = tmp.to_object();
        // std::mem::forget(tmp);
        r
    }];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let node = children.pop().unwrap();
            assert!(children.is_empty());
            let node = if let HIRObject::SpecConstant(spec_constant) = node.construct() {
                spec_constant
            } else {
                panic!("Expected SpecConstant")
            };
            let spec_constant = Term::SpecConstant(node);
            HIRObject::Term(spec_constant)
        }),
    };
    std::mem::forget(node);
    Arc::into_raw(result.into_raw())
}

/// Make a hexadecimal literal (wrapped in a spec constant). For example, `SpecConstant::Hexadecimal(#x7FFA)`.
#[no_mangle]
pub extern "C" fn krpk_make_hex_literal(bytes: *const u8, width_in_bits: u64) -> *const KASTNode {
    assert!(width_in_bits % 4 == 0);
    let bytes = unsafe {
        std::slice::from_raw_parts(
            bytes,
            width_in_bits as usize / 8 + if width_in_bits % 8 == 0 { 0 } else { 1 },
        )
    }
    .to_vec();
    let hex = Hexadecimal {
        bytes,
        digit_num: (width_in_bits / 4) as usize,
    };
    let spec = SpecConstant::Hexadecimal(hex);
    let result = InnerASTNode {
        children: Default::default(),
        construct: Arc::new(move |children| {
            let children = children;
            assert_eq!(0, children.len());
            HIRObject::SpecConstant(spec.clone())
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make an annotated AST node, e.g., `(! some_term :name some_name)`.
#[no_mangle]
pub extern "C" fn krpk_make_annotated(node: *const KASTNode, args: KASTArray) -> *const KASTNode {
    let mut children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    children.push({
        let tmp = unsafe { Arc::from_raw(node) };
        let r = tmp.to_object();
        std::mem::forget(tmp);
        r
    });
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let node = children.pop().unwrap();

            let node = if let HIRObject::Term(term) = node.construct() {
                Box::new(term)
            } else {
                panic!("Expected Term")
            };

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Attribute(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Annotated(node, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(not expr)`.
#[no_mangle]
pub extern "C" fn krpk_make_not(expr: *const KASTNode) -> *const KASTNode {
    let children = vec![__rc_helper(expr).to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("not"))),
            );

            let mut args = vec![];
            let expr = children.pop().unwrap();
            args.push(if let HIRObject::Term(expr) = expr.construct() {
                expr
            } else {
                panic!("Expected Term")
            });
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(and arg1 arg2 arg3...)`.
#[no_mangle]
pub extern "C" fn krpk_make_and(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("and"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_and`].
#[no_mangle]
pub extern "C" fn krpk_make_or(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("or"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_and`].
#[no_mangle]
pub extern "C" fn krpk_make_xor(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("xor"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(= arg1 arg2 arg3...)`.
#[no_mangle]
pub extern "C" fn krpk_make_equal(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("="))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(distinct arg1 arg2 arg3...)`.
#[no_mangle]
pub extern "C" fn krpk_make_distinct(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("distinct"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvand arg1 arg2 arg3...)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvand(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("bvand"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvand`].
#[no_mangle]
pub extern "C" fn krpk_make_bvxor(exprs: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = exprs.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("bvxor"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvand`].
#[no_mangle]
pub extern "C" fn krpk_make_bvor(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("bvor"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvadd arg1 arg2 arg3...)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvadd(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("bvadd"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvadd`].
#[no_mangle]
pub extern "C" fn krpk_make_bvmul(args: KASTArray) -> *const KASTNode {
    let children = {
        let tmp = args.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        // std::mem::forget(tmp);
        r
    };
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let children = children;

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("bvmul"))),
            );

            let mut args = vec![];
            for arg in children {
                args.push(if let HIRObject::Term(arg) = arg.construct() {
                    arg
                } else {
                    panic!("Expected Term")
                });
            }
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    // std::mem::forget(args);
    Arc::into_raw(result.into_raw())
}

/// Make a term `(=> lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_imply(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple(String::from("=>"));
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            // assert_eq!(3, children.len());
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvnot expr)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvnot(expr: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvnot".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let expr = __rc_helper(expr).to_object();
    let result = InnerASTNode {
        children: vec![expr],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let expr = if let HIRObject::Term(expr) = children.pop().unwrap().construct() {
                expr
            } else {
                panic!("Expected Term")
            };
            let args = vec![expr];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

#[no_mangle]
pub extern "C" fn krpk_make_bv2bool(expr: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bv2bool".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let expr = __rc_helper(expr).to_object();
    let result = InnerASTNode {
        children: vec![expr],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let expr = if let HIRObject::Term(expr) = children.pop().unwrap().construct() {
                expr
            } else {
                panic!("Expected Term")
            };
            let args = vec![expr];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

#[no_mangle]
pub extern "C" fn krpk_make_bool2bv(expr: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bool2bv".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let expr = __rc_helper(expr).to_object();
    let result = InnerASTNode {
        children: vec![expr],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let expr = if let HIRObject::Term(expr) = children.pop().unwrap().construct() {
                expr
            } else {
                panic!("Expected Term")
            };
            let args = vec![expr];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(concat lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_concat(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("concat".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvneg expr)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvneg(expr: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvneg".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let expr = __rc_helper(expr).to_object();
    let result = InnerASTNode {
        children: vec![expr],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let expr = if let HIRObject::Term(expr) = children.pop().unwrap().construct() {
                expr
            } else {
                panic!("Expected Term")
            };
            let args = vec![expr];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvudiv lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvudiv(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvudiv".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvudiv`].
#[no_mangle]
pub extern "C" fn krpk_make_bvurem(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvurem".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvshl lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvshl(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvshl".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvlshr`].
#[no_mangle]
pub extern "C" fn krpk_make_bvlshr(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvlshr".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvult lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvult(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvult".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvnand lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvnand(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvnand".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvnand`].
#[no_mangle]
pub extern "C" fn krpk_make_bvnor(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvnor".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvnand`].
#[no_mangle]
pub extern "C" fn krpk_make_bvxnor(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvxnor".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvcomp lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvcomp(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvcomp".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(bvsub lhs rhs)`.
#[no_mangle]
pub extern "C" fn krpk_make_bvsub(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsub".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvudiv`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsdiv(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsdiv".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvudiv`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsrem(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsrem".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvudiv`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsmod(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsmod".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvlshr`].
#[no_mangle]
pub extern "C" fn krpk_make_bvashr(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvashr".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvule(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvule".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvugt(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvugt".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvuge(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvuge".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvslt(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvslt".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsle(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsle".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsgt(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsgt".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_bvult`].
#[no_mangle]
pub extern "C" fn krpk_make_bvsge(lhs: *const KASTNode, rhs: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("bvsge".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let lhs = __rc_helper(lhs).to_object();
    let rhs = __rc_helper(rhs).to_object();
    let result = InnerASTNode {
        children: vec![rhs, lhs],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let lhs = if let HIRObject::Term(rhs) = children.pop().unwrap().construct() {
                rhs
            } else {
                panic!("Expected Term")
            };
            let rhs = if let HIRObject::Term(lhs) = children.pop().unwrap().construct() {
                lhs
            } else {
                panic!("Expected Term")
            };
            let args = vec![lhs, rhs];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

#[no_mangle]
pub extern "C" fn krpk_make_ite(cond: *const KASTNode, then: *const KASTNode, else_: *const KASTNode) -> *const KASTNode {
    let symbol = Symbol::Simple("ite".to_string());
    let func = Identifier::Symbol(symbol);
    let func = QualIdentifier::Simple(func);
    let cond = __rc_helper(cond).to_object();
    let then = __rc_helper(then).to_object();
    let else_ = __rc_helper(else_).to_object();
    let result = InnerASTNode {
        children: vec![else_, then, cond],
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let cond = if let HIRObject::Term(cond) = children.pop().unwrap().construct() {
                cond
            } else {
                panic!("Expected Term")
            };
            let then = if let HIRObject::Term(then) = children.pop().unwrap().construct() {
                then
            } else {
                panic!("Expected Term")
            };
            let else_ = if let HIRObject::Term(else_) = children.pop().unwrap().construct() {
                else_
            } else {
                panic!("Expected Term")
            };
            let args = vec![cond, then, else_];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((extract to from) bitvec)`.
#[no_mangle]
pub extern "C" fn krpk_make_extract(
    from: u64,
    to: u64,
    bitvec: *const KASTNode,
) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let from_index = Index::Numeral(Numeral(from as usize));
    let to_index = Index::Numeral(Numeral(to as usize));
    let symbol = Symbol::Simple("extract".to_string());
    let func = Identifier::Indexed(
        symbol,
        vec![to_index, from_index],
    );
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((repeat times) bitvec)`.
#[no_mangle]
pub extern "C" fn krpk_make_repeat(times: u64, bitvec: *const KASTNode) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let times_index = Index::Numeral(Numeral(times as usize));
    let symbol = Symbol::Simple("repeat".to_string());
    let func = Identifier::Indexed(
        symbol,
        vec![times_index],
    );
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((zero_extend padding) bitvec)`.
#[no_mangle]
pub extern "C" fn krpk_make_zero_extend(padding: u64, bitvec: *const KASTNode) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let padding_index = Index::Numeral(Numeral(padding as usize));
    let symbol = Symbol::Simple("zero_extend".to_string());
    let func = Identifier::Indexed(
        symbol,
        vec![padding_index],
    );
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_zero_extend`].
#[no_mangle]
pub extern "C" fn krpk_make_sign_extend(padding: u64, bitvec: *const KASTNode) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let padding_index = Index::Numeral(Numeral(padding as usize));
    let symbol = Symbol::Simple("sign_extend".to_string());
    let func = Identifier::Indexed(
        symbol,
        vec![padding_index],
    );
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((rotate_left shift) bitvec)`.
#[no_mangle]
pub extern "C" fn krpk_make_rotate_left(shift: u64, bitvec: *const KASTNode) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let shift_index = Index::Numeral(Numeral(shift as usize));
    let symbol = Symbol::Simple("rotate_left".to_string());
    let func = Identifier::Indexed(symbol, vec![shift_index]);
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// See [`krpk_make_rotate_left`].
#[no_mangle]
pub extern "C" fn krpk_make_rotate_right(shift: u64, bitvec: *const KASTNode) -> *const KASTNode {
    let bitvec = __rc_helper(bitvec);
    let shift_index = Index::Numeral(Numeral(shift as usize));
    let symbol = Symbol::Simple("rotate_right".to_string());
    let func = Identifier::Indexed(symbol, vec![shift_index]);
    let func = QualIdentifier::Simple(func);

    let children = vec![bitvec.to_object()];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            let bitvec = if let HIRObject::Term(bitvec) = children.pop().unwrap().construct() {
                bitvec
            } else {
                panic!("Expected Term")
            };

            let args = vec![bitvec];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(select array index)`.
#[no_mangle]
pub extern "C" fn krpk_make_select(
    array: *const KASTNode,
    index: *const KASTNode,
) -> *const KASTNode {
    let children = vec![
        {
            let array = __rc_helper(array);
            array.to_object()
        },
        {
            let index = __rc_helper(index);
            index.to_object()
        },
    ];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(children.len(), 2);

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("select"))),
            );

            let index = if let HIRObject::Term(index) = children.pop().unwrap().construct() {
                index
            } else {
                panic!("Expected Term")
            };
            let array = if let HIRObject::Term(array) = children.pop().unwrap().construct() {
                array
            } else {
                panic!("Expected Term")
            };

            let args = vec![array, index];
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(store array index value)`.
#[no_mangle]
pub extern "C" fn krpk_make_store(
    array: *const KASTNode,
    index: *const KASTNode,
    value: *const KASTNode,
) -> *const KASTNode {
    let children = vec![
        {
            let array = __rc_helper(array);
            array.to_object()
        },
        {
            let index = __rc_helper(index);
            index.to_object()
        },
        {
            let value = __rc_helper(value);
            value.to_object()
        },
    ];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(children.len(), 3);

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("store"))),
            );

            let value = if let HIRObject::Term(value) = children.pop().unwrap().construct() {
                value
            } else {
                panic!("Expected Term")
            };
            let index = if let HIRObject::Term(index) = children.pop().unwrap().construct() {
                index
            } else {
                panic!("Expected Term")
            };
            let array = if let HIRObject::Term(array) = children.pop().unwrap().construct() {
                array
            } else {
                panic!("Expected Term")
            };

            let args = vec![array, index, value];
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `(ensure_index array index)`.
#[no_mangle]
pub extern "C" fn krpk_make_ensure_index(
    array: *const KASTNode,
    ensured_index: *const KASTNode,
) -> *const KASTNode {
    let children = vec![
        {
            let array = __rc_helper(array);
            array.to_object()
        },
        {
            let ensure_index = __rc_helper(ensured_index);
            ensure_index.to_object()
        },
    ];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(children.len(), 2);

            let func = QualIdentifier::Simple(
                Identifier::Symbol(Symbol::Simple(String::from("ensure_index"))),
            );

            let ensured_index = if let HIRObject::Term(ensured_index) = children.pop().unwrap().construct() {
                ensured_index
            } else {
                panic!("Expected Term")
            };
            let array = if let HIRObject::Term(array) = children.pop().unwrap().construct(){
                array
            } else {
                panic!("Expected Term")
            };

            let args = vec![array, ensured_index];
            let term = Term::Apply(func, args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((as const sort) value)`.
#[no_mangle]
pub extern "C" fn krpk_make_array_const(
    sort: *const KASTNode,
    value: *const KASTNode,
) -> *const KASTNode {
    let symbol = Symbol::Simple("const".to_string());
    let func = Identifier::Symbol(symbol);
    let sort = __rc_helper(sort).to_object();
    let sort = if let HIRObject::Sort(sort) = sort.construct() {
        sort
    } else {
        panic!("Expected Sort")
    };
    let func = QualIdentifier::Qualified(func, sort);

    let value = __rc_helper(value).to_object();
    let children = vec![value];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(children.len(), 1);
            let value = if let HIRObject::Term(value) = children.pop().unwrap().construct() {
                value
            } else {
                panic!("Expected Term")
            };
            let args = vec![value];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a term `((as (_ god_save_me_const "hexbytes") sort) value)`.
#[no_mangle]
pub extern "C" fn krpk_make_array_const_with_provided_values(
    sort: *const KASTNode,
    default_value: *const KASTNode,
    provided_values: *const u8,
) -> *const KASTNode {
    let hex_bytes = unsafe {CStr::from_ptr(provided_values as *const i8)}.to_str().unwrap().to_string();
    let symbol = Symbol::Simple("god_save_me_const".to_string());
    let func = Identifier::Indexed(symbol, vec![Index::Symbol(Symbol::Quoted(hex_bytes))]);
    let sort = __rc_helper(sort).to_object();
    let sort = if let HIRObject::Sort(sort) = sort.construct() {
        sort
    } else {
        panic!("Expected Sort")
    };
    let func = QualIdentifier::Qualified(func, sort);

    let value = __rc_helper(default_value).to_object();
    let children = vec![value];
    let result = InnerASTNode {
        children,
        construct: Arc::new(move |children: Vec<InnerASTNode>| {
            let mut children = children;
            assert_eq!(children.len(), 1);
            let value = if let HIRObject::Term(value) = children.pop().unwrap().construct() {
                value
            } else {
                panic!("Expected Term")
            };
            let args = vec![value];
            let term = Term::Apply(func.clone(), args);
            HIRObject::Term(term)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make a declare-const command `(declare-const const_symbol sort)` and return the constant's symbol.
#[no_mangle]
pub extern "C" fn krpk_make_declare_const(
    const_symbol: *const KASTNode,
    sort: *const KASTNode,
) -> *const KASTNode {
    let const_symbol = __rc_helper(const_symbol).to_object();
    let sort = __rc_helper(sort).to_object();
    let resuslt = InnerASTNode {
        children: vec![sort, const_symbol],
        construct: Arc::new(move |children| {
            let mut children = children;
            assert_eq!(children.len(), 2);
            let const_symbol =
                if let HIRObject::Symbol(symbol) = children.pop().unwrap().construct() {
                    symbol
                } else {
                    panic!("Expected QualIdentifier")
                };
            let sort = if let HIRObject::Sort(sort) = children.pop().unwrap().construct() {
                sort
            } else {
                panic!("Expected Sort")
            };
            let declare_const = Command::DeclareConst(const_symbol, sort);
            HIRObject::Command(declare_const)
        }),
    };
    Arc::into_raw(resuslt.into_raw())
}

/// Make a declare-cb command `(declare-cb func_name (param1 param2 ...) return_type)`.
#[no_mangle]
pub extern "C" fn krpk_make_declare_cb(
    cb_symbol: *const KASTNode,
    param_types: KASTArray,
    return_type: *const KASTNode,
) -> *const KASTNode {
    let cb_symbol = __rc_helper(cb_symbol).to_object();
    let param_types = {
        let tmp = param_types.to_vec();
        let r = tmp.iter().rev().map(|x| x.to_object()).collect_vec();
        r
    };
    let return_type = __rc_helper(return_type).to_object();
    let mut children = vec![return_type];
    children.extend(param_types);
    children.push(cb_symbol);
    let resuslt = InnerASTNode {
        children,
        construct: Arc::new(move |children| {
            let mut children = children;
            let cb_symbol = if let HIRObject::Symbol(symbol) = children.pop().unwrap().construct() {
                symbol
            } else {
                panic!("Expected QualIdentifier")
            };
            let mut param_types = vec![];
            assert!(children.len() >= 1);
            while children.len() != 1 {
                let param_type =
                    if let HIRObject::Symbol(sort) = children.pop().unwrap().construct() {
                        sort
                    } else {
                        panic!("Expected Sort")
                    };
                param_types.push(param_type);
            }
            let return_type = if let HIRObject::Symbol(sort) = children.pop().unwrap().construct() {
                sort
            } else {
                panic!("Expected Sort")
            };
            let declare_cb = Command::DeclareCB(cb_symbol, param_types, return_type);
            HIRObject::Command(declare_cb)
        }),
    };
    Arc::into_raw(resuslt.into_raw())
}

/// Make a declare-ctype command `(declare-ctype ctype sort)`.
#[no_mangle]
pub extern "C" fn krpk_make_declare_ctype(
    ctype: *const KASTNode,
    sort: *const KASTNode,
) -> *const KASTNode {
    let ctype = __rc_helper(ctype).to_object();
    let sort = __rc_helper(sort).to_object();
    let resuslt = InnerASTNode {
        children: vec![sort, ctype],
        construct: Arc::new(move |children| {
            let mut children = children;
            assert_eq!(children.len(), 2);
            let ctype = if let HIRObject::Symbol(symbol) = children.pop().unwrap().construct() {
                symbol
            } else {
                panic!("Expected QualIdentifier")
            };
            let sort = if let HIRObject::Sort(sort) = children.pop().unwrap().construct() {
                sort
            } else {
                panic!("Expected Sort")
            };
            let define_ctype = Command::DefineCType(ctype, sort);
            HIRObject::Command(define_ctype)
        }),
    };
    Arc::into_raw(resuslt.into_raw())
}

/// Make an assertion command `(assert term)`.
#[no_mangle]
pub extern "C" fn krpk_make_assertion(term: *const KASTNode) -> *const KASTNode {
    let term = __rc_helper(term).to_object();
    let resuslt = InnerASTNode {
        children: vec![term],
        construct: Arc::new(move |children| {
            let mut children = children;
            assert_eq!(children.len(), 1);
            let term = if let HIRObject::Term(term) = children.pop().unwrap().construct() {
                term
            } else {
                panic!("Expected Term")
            };
            let assertion = Command::Assert(term);
            HIRObject::Command(assertion)
        }),
    };
    Arc::into_raw(resuslt.into_raw())
}

/// Collect all commands into one SMT-LIB 2 script.
#[no_mangle]
pub extern "C" fn krpk_make_smt_script(commands: KASTArray) -> *const KASTNode {
    let commands = {
        let tmp = commands.to_vec();
        let r = tmp.iter().map(|x| x.to_object()).collect_vec();
        r
    };
    let resuslt = InnerASTNode {
        children: commands,
        construct: Arc::new(move |children| {
            let children = children;
            let mut commands = vec![];
            for child in children {
                let command = if let HIRObject::Command(command) = child.construct() {
                    command
                } else {
                    panic!("Expected Command")
                };
                commands.push(command);
            }
            let smt_script = SMTScript(commands);
            HIRObject::SMTScript(smt_script)
        }),
    };
    Arc::into_raw(resuslt.into_raw())
}

/// Convert an AST node to debug string, stored in the buffer. The return value is the length of the string and -1 if
/// the buffer is too small.
#[no_mangle]
pub extern "C" fn krpk_node_debug_fmt(
    node: *const KASTNode,
    buffer: *mut c_char,
    buffer_size: u64,
) -> i64 {
    let node = __rc_helper(node);
    let inner_node = node.to_object();
    // std::mem::forget(node);
    let ast = inner_node.construct();
    let string = CString::new(format!("{:#?}", ast)).unwrap();
    let len = string.as_bytes().len();
    let not_overflow = len < buffer_size as usize;
    if not_overflow {
        unsafe {
            std::ptr::copy_nonoverlapping(string.as_ptr(), buffer as *mut i8, len);
        }
        return len as i64;
    } else {
        unsafe {
            std::ptr::copy_nonoverlapping(
                string.as_ptr(),
                buffer as *mut i8,
                buffer_size as usize - 1,
            );
            *buffer.offset(buffer_size as isize - 1) = 0;
        }
        return -1;
    }
}

/// Make a set-logic command `(set-logic logic)` with 0 corresponding to ALL.
#[no_mangle]
pub extern "C" fn krpk_make_set_logic(logic: u8) -> *const KASTNode {
    let logic = match logic {
        0 => Symbol::Simple("ALL".to_string()),
        _ => unimplemented!(),
    };

    let set_logic = Command::SetLogic(logic);

    let r = InnerASTNode {
        children: vec![],
        construct: Arc::new(move |children| {
            assert!(children.is_empty());
            HIRObject::Command(set_logic.clone())
        }),
    };
    Arc::into_raw(r.into_raw())
}

/// Make a set-arch command `(set-arch arch)` with 0 corresponding to X86.
#[no_mangle]
pub extern "C" fn krpk_make_set_arch(arch: u8) -> *const KASTNode {
    let arch = match arch {
        0 => Symbol::Simple("X86".to_string()),
        _ => unimplemented!(),
    };
    let result = InnerASTNode {
        children: vec![],
        construct: Arc::new(move |children| {
            assert_eq!(0, children.len());
            let set_arch = Command::SetArch(arch.clone());
            HIRObject::Command(set_arch)
        }),
    };
    Arc::into_raw(result.into_raw())
}

/// Make an alloc command `(alloc addr size term)`. The width of the term should be less than the size.
/// The term must be sized, so terms with sorts like `(Array (_ BitVec 32) (_ BitVec 8))` are not allowed because they
/// do not have an exact size.
#[no_mangle]
pub extern "C" fn krpk_make_alloc(
    addr: *const KASTNode,
    size: u64,
    term: *const KASTNode,
) -> *const KASTNode {
    let addr = __rc_helper(addr).to_object();
    let term = __rc_helper(term).to_object();
    let result = InnerASTNode {
        children: vec![addr, term],
        construct: Arc::new(move |children| {
            assert_eq!(2, children.len());
            let mut children = children;
            let term = if let HIRObject::Term(term) = children.pop().unwrap().construct() {
                term
            } else {
                panic!("Expected Term")
            };
            let HIRObject::Term(addr) = children.pop().unwrap().construct() else {
                panic!("Expected Term")
            };
            let Term::SpecConstant(addr) = addr else {
                panic!("Expected Hexadecimal")
            };
            let SpecConstant::Hexadecimal(addr) = addr else {
                panic!("Expected Hexadecimal")
            };
            let size = Numeral(size as usize);
            let alloc = Command::Alloc(addr, size, MemoryCell::Term(term));
            HIRObject::Command(alloc)
        }),
    };
    Arc::into_raw(result.into_raw())
}


#[no_mangle]
pub extern "C" fn krpk_make_alloc_seg(
    addr: *const KASTNode,
    size: u64,
    hex_bytes: *const u8,
) -> *const KASTNode {
    let addr = __rc_helper(addr).to_object();
    let hex_bytes = unsafe {CStr::from_ptr(hex_bytes as *const i8)}.to_str().unwrap().to_string();
    let result = InnerASTNode {
        children: vec![addr],
        construct: Arc::new(move |children| {
            assert_eq!(1, children.len());
            let mut children = children;
            let HIRObject::Term(addr) = children.pop().unwrap().construct() else {
                panic!("Expected Term")
            };
            let Term::SpecConstant(addr) = addr else {
                panic!("Expected Hexadecimal")
            };
            let SpecConstant::Hexadecimal(addr) = addr else {
                panic!("Expected Hexadecimal")
            };
            let size = Numeral(size as usize);
            let alloc = Command::Alloc(addr, size, MemoryCell::HexBytes(StringLiteral(hex_bytes.clone())));
            HIRObject::Command(alloc)
        }),
    };
    Arc::into_raw(result.into_raw())
}
