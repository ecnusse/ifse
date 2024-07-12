use std::borrow::Borrow;
use std::cell::{Cell, Ref, RefCell, RefMut};
use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::mem;

use std::rc::{Rc, Weak};

use itertools::Itertools;
use multiset::HashMultiSet;

thread_local! {
    static IR_REF_ID_COUNT: Cell<isize> = Default::default();
    static IR_REF_ID_REGISTER: RefCell<HashMap<u64, isize>> = Default::default();
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    BitVec(usize),

    /// Array in the form `(Array (_ BitVec m) (_ BitVec n))`
    /// with a finite upper bound of sort `u` where `u` is the u64 interpretation of max possible domain values.
    /// If `u` is `None`, then the domain is unbounded. This may happen when the array is a constant array.
    BitVecArray {
        domain_width: usize,
        range_width: usize,
        upper_bound: Option<u64>,
    },
    Bool,
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use Type::*;
        match (self, other) {
            (Bool, Bool) => Some(std::cmp::Ordering::Equal),
            (Bool, _) => Some(std::cmp::Ordering::Less),
            (_, Bool) => Some(std::cmp::Ordering::Greater),
            (BitVec(n), BitVec(m)) => n.partial_cmp(m),
            (BitVec(_), _) => Some(std::cmp::Ordering::Less),
            (_, BitVec(_)) => Some(std::cmp::Ordering::Greater),
            (BitVecArray { .. }, BitVecArray { .. }) => todo!(),
        }
    }
}

impl Ord for Type {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;
        match self {
            BitVec(n) => write!(f, "BitVec<{}>", n),
            BitVecArray {
                domain_width,
                range_width,
                upper_bound,
            } => {
                write!(
                    f,
                    "BitVecArray<{}, {}, {}>",
                    domain_width,
                    range_width,
                    if let Some(upper_bound) = upper_bound {
                        upper_bound.to_string()
                    } else {
                        "unknown".to_string()
                    }
                )
            }
            Bool => write!(f, "Bool"),
        }
    }
}

impl Type {
    pub fn size_in_bits(&self) -> Option<usize> {
        match self {
            Self::BitVec(n) => Some(*n),
            Self::BitVecArray {
                range_width,
                upper_bound,
                ..
            } => Some((upper_bound.clone()? as usize + 1) * range_width),
            Self::Bool => Some(1),
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            Self::Bool => true,
            _ => false,
        }
    }

    pub fn is_bitvec(&self) -> bool {
        match self {
            Self::BitVec(_) => true,
            _ => false,
        }
    }

    pub fn is_bitvec_array(&self) -> bool {
        match self {
            Self::BitVecArray { .. } => true,
            _ => false,
        }
    }

    pub fn bitvec_array_domain_width(&self) -> Option<usize> {
        match self {
            Self::BitVecArray { domain_width, .. } => Some(*domain_width),
            _ => None,
        }
    }

    pub fn bitvec_array_range_width(&self) -> Option<usize> {
        match self {
            Self::BitVecArray { range_width, .. } => Some(*range_width),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord)]
pub enum LiteralValue {
    BitVecValue(usize, Vec<u8>),
    BitVecArrayValue(usize, usize, Vec<Vec<u8>>),
    BoolValue(bool),
}

impl PartialOrd for LiteralValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use LiteralValue::*;
        match (self, other) {
            (BoolValue(a), BoolValue(b)) => a.partial_cmp(b),
            (BoolValue(_), _) => Some(std::cmp::Ordering::Less),
            (_, BoolValue(_)) => Some(std::cmp::Ordering::Greater),
            (BitVecValue(n, a), BitVecValue(m, b)) => {
                if n < m {
                    return Some(std::cmp::Ordering::Less);
                } else if n > m {
                    return Some(std::cmp::Ordering::Greater);
                }
                a.partial_cmp(b)
            }
            (BitVecValue(..), _) => Some(std::cmp::Ordering::Less),
            (_, BitVecValue(..)) => Some(std::cmp::Ordering::Greater),
            (BitVecArrayValue(..), BitVecArrayValue(..)) => todo!(),
        }
    }
}

fn usize_to_hex(width_in_bytes: usize, value: usize) -> String {
    let mut result = "#x".to_string();
    for i in (0..width_in_bytes).rev() {
        let byte = (value >> (i * 8)) & 0xff;
        result.push_str(&format!("{:02x}", byte));
    }
    result
}

impl fmt::Display for LiteralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LiteralValue::*;
        match self {
            BitVecValue(size, value) => {
                write!(f, "#x")?;
                let last_byte_in_bits = if *size % 8 == 0 { 8 } else { *size % 8 };
                let mut first = true;
                for byte in value.iter().rev() {
                    if first {
                        first = false;
                        write!(f, "{:02x}", byte & (0xFF >> (8 - last_byte_in_bits)))?;
                    } else {
                        write!(f, "{:02x}", byte)?;
                    }
                }
                Ok(())
            }
            BitVecArrayValue(domain_width, range_width, value) => {
                write!(f, "[")?;
                for i in 0..value.len() {
                    let domain_in_bytes = *domain_width / 8;
                    let range_in_bytes = *range_width / 8;
                    write!(f, "{} => #x", usize_to_hex(domain_in_bytes, i))?;
                    for j in (0..range_in_bytes).rev() {
                        write!(f, "{:02x}", value[i][j])?;
                    }
                    write!(f, ", ")?;
                }
                write!(f, "]")
            }
            BoolValue(value) => write!(f, "{}", value),
        }
    }
}

impl LiteralValue {
    pub fn type_(&self) -> Type {
        match self {
            LiteralValue::BitVecValue(size, _) => Type::BitVec(*size),
            LiteralValue::BitVecArrayValue(domain_width, range_width, _) => Type::BitVecArray {
                domain_width: *domain_width,
                range_width: *range_width,
                upper_bound: None,
            },
            LiteralValue::BoolValue(_) => Type::Bool,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Ord)]
pub struct DeclaredConstant {
    pub name: String,
    pub type_: Type,

    virtual_bytes: RefCell<BTreeSet<usize>>,
}

impl Hash for DeclaredConstant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.type_.hash(state);
        self.virtual_bytes().hash(state);
    }
}

impl PartialOrd for DeclaredConstant {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let a = self.name.partial_cmp(&other.name)?;
        if a != std::cmp::Ordering::Equal {
            return Some(a);
        }
        self.type_.partial_cmp(&other.type_)
    }
}

impl DeclaredConstant {
    pub fn new(name: String, type_: Type) -> Self {
        Self {
            name,
            type_,
            virtual_bytes: Default::default(),
        }
    }

    pub fn size_in_bits(&self) -> usize {
        self.type_.size_in_bits().unwrap()
    }

    pub fn size_in_bytes(&self) -> usize {
        self.size_in_bits() / 8 + if self.size_in_bits() % 8 == 0 { 0 } else { 1 }
    }

    pub(crate) fn set_virtual(&self, from: usize, to: usize) {
        for i in from..to {
            self.virtual_bytes.borrow_mut().insert(i);
        }
    }

    pub(crate) fn unset_virtual(&self, from: usize, to: usize) {
        for i in from..to {
            self.virtual_bytes.borrow_mut().remove(&i);
        }
    }

    pub fn virtual_bytes(&self) -> Vec<usize> {
        let mut r = self.virtual_bytes.borrow().iter().cloned().collect_vec();
        r.sort();
        r
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DeclaredCBFunction {
    pub id: String,
    pub params: Vec<(Type, String)>,
    pub return_smt_and_c_type: (Type, String),
}

#[derive(Debug, Clone)]
pub struct ValueRef {
    id: usize,
    ir: RefCell<Weak<RefCell<IR>>>,
}

impl PartialEq for ValueRef {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ValueRef {}

impl Display for ValueRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "expr_{}", self.id)
    }
}

thread_local! {
    static VALUE_REF_ID_COUNT: Cell<usize> = Default::default();
}

#[cfg(test)]
/// When running multiple unit tests, accumulation of the counter may make the result non-deterministic. Thus, it must
/// be reset in each test case.
/// TODO: This might be unnecessary after making `REF_ID_COUNT` thread local?
pub(crate) fn reset_ref_id_count() {
    // REF_ID_COUNT.store(0, std::sync::atomic::Ordering::SeqCst);
    VALUE_REF_ID_COUNT.with(|ref_id_count| ref_id_count.set(0));
    IR_REF_ID_COUNT.with(|ref_id_count| ref_id_count.set(0));
}

impl ValueRef {
    fn empty() -> Self {
        Self {
            id: VALUE_REF_ID_COUNT.with(|value_ref_id_count| {
                let id = value_ref_id_count.get();
                value_ref_id_count.set(id + 1);
                id
            }),
            ir: RefCell::new(Weak::new()),
        }
    }

    fn set_value(&self, value: &Rc<RefCell<IR>>) {
        self.ir.replace(Rc::downgrade(value));
    }

    pub fn id(&self) -> usize {
        self.id
    }
}

impl Hash for ValueRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

thread_local! {
    static TYPE_CACHE: RefCell<HashMap<ValueRef, Type>> = Default::default();
}

impl ValueRef {
    pub fn type_(&self) -> Type {
        let lookup = TYPE_CACHE.with(|type_cache| type_cache.borrow().get(self).cloned());
        if let Some(type_) = lookup {
            return type_;
        }
        let type_ = self.ir().borrow().type_();
        TYPE_CACHE.with(|type_cache| {
            type_cache.borrow_mut().insert(self.clone(), type_.clone());
        });
        type_
    }

    pub fn ir(&self) -> MutableIRRef {
        Weak::upgrade(&RefCell::borrow(&self.ir).clone())
            .unwrap()
            .into()
    }
}

#[derive(Debug, Clone)]
pub enum IRKind {
    Check,
    Memset(u64, Option<String>),
    WriteBack(Rc<DeclaredConstant>),

    ConstantRef(Rc<DeclaredConstant>),
    Literal { literal: LiteralValue },
    Not,
    And,
    Or,
    Eq,
    Ne, // `bne a b` can be translate to `a != b` and such a form is more concise than a trivial `!(a == b)`, so we keep this instruction.
    Ite,
    CallCBFunction(Rc<DeclaredCBFunction>),

    // The above data structures are for parsing the core function,
    // the following are for bit vec, see more details in `qf_bv_function` in semantics.rs
    // KRPKIdentifier::Symbol
    Concat,
    BVNot,
    BVAnd,
    BVOr,
    BVNeg,
    BVAdd,
    BVMul,
    BVUDiv,
    BVURem,
    BVShL,
    BVLShR,
    BVULt,
    // BVNand, which is redundant since BVNand a = BVNot (BVAnd a).
    // BVNor, which is redundant since BVNor a = BVNot (BVOr a).
    // BVXor, which is redundant since BVXor a b = (BVAnd (BVNot a) b) BVOr (BVAnd a (BVNot b)).
    // BVXnor, which is redundant since BVXnor a b = (a BVAnd b) BVOr ((BVNot a) BVAnd (BVNot b)).
    BVComp,
    BVSub,
    BVSDiv,
    BVSRem,
    BVSMod,
    BVAShR,
    BVULe,
    BVUGt,
    BVUGe,
    BVSLt,
    BVSLe,
    BVSGt,
    BVSGe,

    // (from, to, bitvec_to_extract)
    Extract(usize, usize),

    // KRPKIdentifier::Indexed (Word operations)
    // This operations are not in [SMT-LIB Standard](https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)
    // However, they can be found in [Microsoft Z3 Doc](https://microsoft.github.io/z3guide/docs/theories/Bitvectors)
    Repeat(usize),
    ZeroExtend(usize),
    SignExtend(usize),
    RotateLeft(usize),
    RotateRight(usize),

    BV2Bool,
    Bool2BV,

    // The below is about ArrayEx, for now just consider arrays whose domain and range are both `Bitvector` such as `Select`
    // REFERENCE: [SMT-LIB ArrayEx](https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml)
    Select,
    Store,
    ConstBVArray(usize, usize),

    Alias,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeInferenceResult {
    ValueType(Type),
    NoValue,
    Err,
}

impl TypeInferenceResult {
    pub fn when(&self, cond: bool) -> Self {
        if cond {
            self.clone()
        } else {
            TypeInferenceResult::Err
        }
    }

    pub fn cond_on(cond: bool, t: Type) -> Self {
        if cond {
            TypeInferenceResult::ValueType(t)
        } else {
            TypeInferenceResult::Err
        }
    }

    // Use closure to enable lazy evaluation (short-circuit)
    pub fn cond_on_with(cond: bool, f: impl FnOnce() -> Type) -> Self {
        if cond {
            TypeInferenceResult::ValueType(f())
        } else {
            TypeInferenceResult::Err
        }
    }

    pub fn unwrap(self) -> Type {
        match self {
            TypeInferenceResult::ValueType(t) => t,
            Self::NoValue => panic!("unwrap a uninitialized type"),
            Self::Err => panic!("unwrap a error type"),
        }
    }
}

impl From<bool> for TypeInferenceResult {
    fn from(b: bool) -> Self {
        if b {
            TypeInferenceResult::NoValue
        } else {
            TypeInferenceResult::Err
        }
    }
}

impl From<Type> for TypeInferenceResult {
    fn from(t: Type) -> Self {
        TypeInferenceResult::ValueType(t)
    }
}

impl IRKind {
    pub fn infer_type(&self, operand_types: &[Type]) -> TypeInferenceResult {
        type TIResult = TypeInferenceResult;
        use IRKind::*;
        match_template! {
            BOOL_BI_OP = [And, Or],
            BV_BI_OP = [BVAnd, BVOr, BVAdd, BVMul, BVUDiv, BVURem, BVShL, BVLShR, BVSub, BVSDiv, BVSRem,
                        BVSMod, BVAShR],
            GENERIC_COMP = [Eq, Ne],
            BV_BI_PRED = [BVULt, BVULe, BVUGt, BVUGe, BVSLt, BVSLe, BVSGt, BVSGe],
            BV_UNI_OP = [BVNot, BVNeg,],
            BV_EXT = [ZeroExtend, SignExtend],
            BV_ROT = [RotateLeft, RotateRight],
            match self {
                BOOL_BI_OP => TIResult::cond_on(
                    operand_types.len() == 2
                        && operand_types[0].is_bool()
                        && operand_types[1].is_bool(),
                    Type::Bool,
                ),
                BV_BI_OP => TIResult::cond_on_with(
                    operand_types.len() == 2
                        && operand_types[0].is_bitvec()
                        && operand_types[0] == operand_types[1],
                    || operand_types[0].clone(),
                ),
                GENERIC_COMP => TIResult::cond_on_with(
                    operand_types.len() == 2 && operand_types[0] == operand_types[1],
                    || Type::Bool,
                ),
                BV_BI_PRED => TIResult::cond_on_with(
                    operand_types.len() == 2
                        && operand_types[0].is_bitvec()
                        && operand_types[0] == operand_types[1],
                    || Type::Bool,
                ),
                BV_UNI_OP => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bitvec(),
                    || operand_types[0].clone(),
                ),
                BV_EXT(padding) => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bitvec(),
                    || Type::BitVec(operand_types[0].size_in_bits().unwrap() + padding),
                ),
                BV_ROT(_useless) => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bitvec(),
                    || operand_types[0].clone(),
                ),
                BVComp => TIResult::cond_on_with(
                    operand_types.len() == 2
                        && operand_types[0].is_bitvec()
                        && operand_types[0] == operand_types[1],
                    || Type::BitVec(1),
                ),
                Ite => TIResult::cond_on_with(
                    operand_types.len() == 3
                        && operand_types[0].is_bool()
                        && operand_types[1] == operand_types[2],
                    || operand_types[1].clone(),
                ),
                CallCBFunction(func) => {
                    let param_types = func.params.iter().map(|(t, _)| t.clone()).collect_vec();
                    let return_type = func.return_smt_and_c_type.0.clone();
                    TIResult::cond_on(operand_types == param_types.as_slice(), return_type)
                }
                Concat => TIResult::cond_on_with(
                    operand_types.len() == 2
                        && operand_types[0].is_bitvec()
                        && operand_types[1].is_bitvec(),
                    || {
                        Type::BitVec(
                            operand_types[0].size_in_bits().unwrap()
                                + operand_types[1].size_in_bits().unwrap(),
                        )
                    },
                ),
                Check => (operand_types.len() == 1 && operand_types[0].is_bool()).into(),
                Memset(_, lit) => {
                    if let Some(_) = lit {
                        (operand_types.len() == 0).into()
                    } else {
                        (operand_types.len() == 1 && operand_types[0].is_bitvec()).into()
                    }
                }
                WriteBack(cst) => {
                    (operand_types.len() == 1 && cst.type_ == operand_types[0]).into()
                }
                ConstantRef(cst) => {
                    TIResult::cond_on(operand_types.len() == 0, cst.type_.clone())
                }
                Literal { literal } => {
                    TIResult::cond_on(operand_types.len() == 0, literal.type_())
                }
                Not => TIResult::cond_on(
                    operand_types.len() == 1 && operand_types[0].is_bool(),
                    Type::Bool,
                ),
                Extract(from, to) => TIResult::cond_on_with(
                    operand_types.len() == 1
                        && operand_types[0].is_bitvec()
                        && *from <= *to
                        && *to < operand_types[0].size_in_bits().unwrap(),
                    || Type::BitVec(*to - *from + 1),
                ),
                Repeat(times) => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bitvec(),
                    || Type::BitVec(operand_types[0].size_in_bits().unwrap() * times),
                ),
                BV2Bool => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bitvec() && operand_types[0].size_in_bits().unwrap() == 1,
                    || Type::Bool,
                ),
                Bool2BV => TIResult::cond_on_with(
                    operand_types.len() == 1 && operand_types[0].is_bool(),
                    || Type::BitVec(1),
                ),
                Select => TIResult::cond_on_with(
                    operand_types.len() == 2
                        && operand_types[0].is_bitvec_array()
                        && operand_types[1].is_bitvec()
                        && operand_types[0].bitvec_array_domain_width().unwrap() == operand_types[1].size_in_bits().unwrap(),
                    || Type::BitVec(operand_types[0].bitvec_array_range_width().unwrap()),
                ),
                Store => TIResult::cond_on_with(
                    operand_types.len() == 3
                        && operand_types[0].is_bitvec_array()
                        && operand_types[1].is_bitvec()
                        && operand_types[0].bitvec_array_domain_width().unwrap() == operand_types[1].size_in_bits().unwrap()
                        && operand_types[0].bitvec_array_range_width().unwrap() == operand_types[2].size_in_bits().unwrap(),
                    || operand_types[0].clone(),
                ),
                ConstBVArray(domain_width, range_width) => TIResult::cond_on_with(
                    operand_types.len() == 1
                        && operand_types[0].is_bitvec()
                        && *range_width == operand_types[0].size_in_bits().unwrap(),
                    || Type::BitVecArray{domain_width: *domain_width, range_width: *range_width, upper_bound: None},
                ),
                Alias => TIResult::cond_on(
                    operand_types.len() == 1,
                    operand_types[0].clone(),
                ),
            }
        }
    }
}

// struct TransparentIRRef(MutableIRRef);

// impl PartialEq for TransparentIRRef {
//     fn eq(&self, other: &Self) -> bool {
//         Rc::ptr_eq(&self.0.ir, &other.0.ir)
//     }
// }

// impl Eq for TransparentIRRef {}

// impl Hash for TransparentIRRef {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         Rc::as_ptr(&self.0.ir).hash(state);
//     }
// }

// struct TransparentIRWeak(MutableIRWeak);

#[derive(Clone, Debug)]
pub struct IR {
    kind: IRKind,
    operands: Vec<ValueRef>,
    refed_by: RefCell<HashMultiSet<MutableIRRef>>,
    depend_on: RefCell<HashMultiSet<MutableIRWeak>>,
    value_ref: Option<ValueRef>,
}

impl Display for IR {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use IRKind::*;
        match_template! {
            SIMPLE = [
                And => "and",
                Or => "or",
                Eq => "eq",
                Ne => "ne",
                Ite => "ite",
                Concat => "concat",
                BVNot => "bvnot",
                BVAnd => "bvand",
                BVOr => "bvor",
                BVNeg => "bvneg",
                BVAdd => "bvadd",
                BVMul => "bvmul",
                BVUDiv => "bvudiv",
                BVURem => "bvurem",
                BVShL => "bvshl",
                BVLShR => "bvlshr",
                BVULt => "bvult",
                BVComp => "bvcomp",
                BVSub => "bvsub",
                BVSDiv => "bvsdiv",
                BVSRem => "bvsrem",
                BVSMod => "bvsmod",
                BVAShR => "bvashr",
                BVULe => "bvule",
                BVUGt => "bvugt",
                BVUGe => "bvuge",
                BVSLt => "bvslt",
                BVSLe => "bvsle",
                BVSGt => "bvsgt",
                BVSGe => "bvsge",
                BV2Bool => "bv2bool",
                Bool2BV => "bool2bv",
                Select => "select",
                Store => "store",
                Not => "not"
            ],
            UNARY_INDEX = [
                Repeat => "repeat",
                ZeroExtend => "zero_extend",
                SignExtend => "sign_extend",
                RotateLeft => "rotate_left",
                RotateRight => "rotate_right"
            ],
            BINARY_INDEX = [
                Extract => "extract",
                ConstBVArray => "constbva"
            ],
            match &self.kind {
                SIMPLE => {
                    write!(f, "{} = {}", self.value_ref.as_ref().unwrap(), SIMPLE)?;
                    for operand in &self.operands {
                        write!(f, " {}", operand)?;
                    }
                    Ok(())
                }
                UNARY_INDEX(index) => {
                    write!(f, "{} = {} {}", self.value_ref.as_ref().unwrap(), UNARY_INDEX, *index);
                    for operand in &self.operands {
                        write!(f, " {}", operand)?;
                    }
                    Ok(())
                },
                BINARY_INDEX(index1, index2) => {
                    write!(f, "{} = {} {} {}", self.value_ref.as_ref().unwrap(), BINARY_INDEX, *index1, *index2);
                    for operand in &self.operands {
                        write!(f, " {}", operand)?;
                    }
                    Ok(())
                },
                Check => {
                    write!(f, "cktrue {}", self.operands[0])
                },
                Memset(addr, bytes) => if let Some(bytes) = bytes {
                    write!(f, "memset {} \"{}\"", addr, bytes)
                } else {
                    write!(f, "memset {} {}", addr, self.operands[0])
                },
                WriteBack(declared) => {
                    write!(f, "writeback {} {}", declared.name, self.operands[0])
                },
                ConstantRef(declared) => {
                    write!(f, "{} = {}", self.value_ref.as_ref().unwrap(), declared.name)
                },
                Literal { literal } => {
                    write!(f, "{} = ", self.value_ref.as_ref().unwrap())?;
                    match literal {
                        LiteralValue::BitVecValue(size, value) => {
                            write!(f, "bvx{}#", size)?;
                            for byte in value.iter().rev() {
                                write!(f, "{:02x}", byte)?;
                            }
                            Ok(())
                        }
                        LiteralValue::BitVecArrayValue(_domain_width, _range_width, _value) => {
                            todo!()
                        }
                        LiteralValue::BoolValue(value) => write!(f, "{}", value),
                    }
                },
                CallCBFunction(cb) => {
                    write!(f, "{} = ({}", self.value_ref.as_ref().unwrap(), cb.id)?;
                    for operand in self.operands.iter() {
                        write!(f, " {}", operand)?;
                    }
                    write!(f, ")")
                },
                Alias => {
                    write!(f, "{} = {}", self.value_ref.as_ref().unwrap(), self.operands[0])
                },
            }
        }
    }
}

impl IR {
    pub fn new(kind: IRKind, operands: Vec<ValueRef>) -> MutableIRRef {
        use IRKind::*;
        let value_ref = match &kind {
            Check | Memset(..) | WriteBack(..) => None,
            _ => Some(ValueRef::empty()),
        };
        let ir_ref = MutableIRRef::from(IR {
            kind,
            operands,
            refed_by: RefCell::new(HashMultiSet::new()),
            value_ref,
            depend_on: RefCell::new(HashMultiSet::new()),
        });

        {
            let tmp = ir_ref.ir.clone();
            if let Some(r) = &ir_ref.borrow().value_ref {
                r.set_value(&tmp)
            }
        }

        for operand in ir_ref.borrow().operands() {
            operand.ir().add_refed(ir_ref.clone());
        }

        ir_ref.into()
    }

    fn refed_by(&self) -> Ref<HashMultiSet<MutableIRRef>> {
        RefCell::borrow(&self.refed_by)
    }

    pub fn type_(&self) -> Type {
        self.kind
            .infer_type(&self.operands.iter().map(|v| v.type_()).collect_vec())
            .unwrap()
    }

    pub fn operands(&self) -> &[ValueRef] {
        &self.operands
    }

    pub fn predecessors<'a>(&'a self) -> impl Iterator<Item = IRRef> + 'a {
        self.depend_on
            .borrow()
            .distinct_elements()
            .map(|k| k.clone().into())
            .collect_vec()
            .into_iter()
    }

    pub fn predecessor_num(&self) -> usize {
        self.predecessors().count()
    }

    pub fn kind(&self) -> &IRKind {
        &self.kind
    }

    pub fn successors<'a>(&'a self) -> impl Iterator<Item = IRRef> + 'a {
        self.refed_by()
            .distinct_elements()
            .map(|ir| ir.clone().into())
            .collect_vec()
            .into_iter()
    }

    pub fn successor_num(&self) -> usize {
        self.successors().count()
    }

    pub fn value_ref(&self) -> Option<ValueRef> {
        self.value_ref.clone()
    }
}

#[derive(Clone, Debug)]
pub struct IRRef {
    inner: MutableIRRef,
}

impl IRRef {
    pub fn borrow(&self) -> Ref<IR> {
        self.inner.borrow()
    }
}

impl From<MutableIRWeak> for IRRef {
    fn from(ir: MutableIRWeak) -> Self {
        Self {
            inner: ir.try_into().unwrap(),
        }
    }
}

impl From<MutableIRRef> for IRRef {
    fn from(ir: MutableIRRef) -> Self {
        Self { inner: ir }
    }
}

impl Into<MutableIRRef> for IRRef {
    fn into(self) -> MutableIRRef {
        self.inner
    }
}

impl PartialEq for IRRef {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for IRRef {}

impl Hash for IRRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl PartialOrd for IRRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.inner.cmp(&other.inner))
    }
}

impl Ord for IRRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

#[derive(Clone, Debug)]
pub struct MutableIRWeak {
    ir: Weak<RefCell<IR>>,
}

impl MutableIRWeak {
    pub fn is_empty(&self) -> bool {
        self.ir.strong_count() == 0
    }

    pub fn empty() -> Self {
        Self { ir: Weak::new() }
    }
}

impl PartialEq for MutableIRWeak {
    fn eq(&self, other: &Self) -> bool {
        Weak::ptr_eq(&self.ir, &other.ir)
    }
}

impl Eq for MutableIRWeak {}

impl Hash for MutableIRWeak {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Weak::as_ptr(&self.ir).hash(state);
    }
}

impl From<MutableIRRef> for MutableIRWeak {
    fn from(ir: MutableIRRef) -> Self {
        Self {
            ir: Rc::downgrade(&ir.ir),
        }
    }
}

impl From<IRRef> for MutableIRWeak {
    fn from(ir: IRRef) -> Self {
        Self {
            ir: Rc::downgrade(&ir.inner.ir),
        }
    }
}

impl TryFrom<MutableIRWeak> for MutableIRRef {
    type Error = ();

    fn try_from(value: MutableIRWeak) -> Result<Self, Self::Error> {
        if let Some(ir) = value.ir.upgrade() {
            Ok(Self { ir })
        } else {
            Err(())
        }
    }
}

impl PartialOrd for MutableIRWeak {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        #[cfg(test)]
        return IR_REF_ID_REGISTER.with(|reg| {
            let reg = reg.borrow();
            let id1 = reg.get(&(self.ir.as_ptr() as u64)).unwrap();
            let id2 = reg.get(&(other.ir.as_ptr() as u64)).unwrap();
            id1.partial_cmp(&id2)
        });
        self.ir.as_ptr().partial_cmp(&other.ir.as_ptr())
    }
}

impl Ord for MutableIRWeak {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        #[cfg(test)]
        return IR_REF_ID_REGISTER.with(|reg| {
            let reg = reg.borrow();
            let id1 = reg.get(&(self.ir.as_ptr() as u64)).unwrap();
            let id2 = reg.get(&(other.ir.as_ptr() as u64)).unwrap();
            id1.cmp(&id2)
        });
        self.ir.as_ptr().cmp(&other.ir.as_ptr())
    }
}

#[derive(Clone, Debug)]
pub struct MutableIRRef {
    ir: Rc<RefCell<IR>>,
}

impl MutableIRRef {
    pub fn borrow(&self) -> Ref<IR> {
        RefCell::borrow(&self.ir)
    }
}

impl MutableIRRef {
    pub fn borrow_mut(&self) -> RefMut<IR> {
        RefCell::borrow_mut(&self.ir)
    }
}

impl PartialOrd for MutableIRRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        #[cfg(test)]
        return IR_REF_ID_REGISTER.with(|reg| {
            let reg = reg.borrow();
            let id1 = reg.get(&(self.ir.as_ptr() as u64)).unwrap();
            let id2 = reg.get(&(other.ir.as_ptr() as u64)).unwrap();
            id1.partial_cmp(&id2)
        });
        self.ir.as_ptr().partial_cmp(&other.ir.as_ptr())
    }
}

impl Ord for MutableIRRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        #[cfg(test)]
        return IR_REF_ID_REGISTER.with(|reg| {
            let reg = reg.borrow();
            let id1 = reg.get(&(self.ir.as_ptr() as u64)).unwrap();
            let id2 = reg.get(&(other.ir.as_ptr() as u64)).unwrap();
            id1.cmp(&id2)
        });
        self.ir.as_ptr().cmp(&other.ir.as_ptr())
    }
}

impl From<Rc<RefCell<IR>>> for MutableIRRef {
    fn from(ir: Rc<RefCell<IR>>) -> Self {
        #[cfg(test)]
        {
            let id = IR_REF_ID_COUNT.with(|ir_ref_id_count| {
                let id = ir_ref_id_count.get();
                ir_ref_id_count.set(id - 1);
                id
            });
            IR_REF_ID_REGISTER.with(|ref_register| {
                let mut tmp = ref_register.borrow_mut();
                if !tmp.contains_key(&(ir.as_ptr() as u64)) {
                    tmp.insert(ir.as_ptr() as u64, id);
                }
            });
        }
        Self { ir }
    }
}

impl Into<Rc<RefCell<IR>>> for MutableIRRef {
    fn into(self) -> Rc<RefCell<IR>> {
        self.ir
    }
}

impl From<IR> for MutableIRRef {
    fn from(ir: IR) -> Self {
        Self::from(Rc::new(RefCell::new(ir)))
    }
}

impl Hash for MutableIRRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ir.as_ptr().hash(state);
    }
}

impl PartialEq for MutableIRRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.ir, &other.ir)
    }
}

impl Eq for MutableIRRef {}

impl MutableIRRef {
    pub fn rewire_to(&self, old: ValueRef, new: ValueRef) {
        let mut new_operands = Vec::new();
        let old_operands = mem::take(&mut self.borrow_mut().operands);
        let mut is_operand = false;
        for operand in old_operands {
            if operand == old {
                is_operand = true;
                new_operands.push(new.clone());
                old.ir().remove_refed(self);
                new.ir().add_refed(self.clone());
            } else {
                new_operands.push(operand);
            }
        }
        let _ = mem::replace(&mut self.borrow_mut().operands, new_operands);
        if is_operand {
            return;
        }
        let t = self
            .borrow()
            .depend_on
            .borrow()
            .iter()
            .filter(|t| {
                let ir: MutableIRRef = (*t).clone().try_into().unwrap();
                ir.borrow().value_ref().is_some() && ir.borrow().value_ref().unwrap() == old
            })
            .cloned()
            .collect_vec();
        assert!(!t.is_empty());
        for d in t {
            let ir: MutableIRRef = d.clone().try_into().unwrap();
            ir.remove_refed(self);
            new.ir().add_refed(self.clone());
        }
    }

    pub fn remove_refed(&self, to_remove: &MutableIRRef) {
        let r = RefCell::borrow_mut(&self.borrow().refed_by).remove(to_remove);
        assert!(r);
        let r = RefCell::borrow_mut(&to_remove.borrow().depend_on).remove(&self.clone().into());
        assert!(r);
    }

    fn remove_depend_on(&self, to_remove: &MutableIRWeak) {
        let r = RefCell::borrow_mut(&self.borrow().depend_on).remove(&to_remove);
        assert!(r);
    }

    pub fn remove_refed_that(&self, predicate: impl Fn(&MutableIRRef) -> bool) -> bool {
        let _r = false;
        let mut to_remove = Vec::new();
        for d in self.borrow().refed_by.borrow().iter() {
            if predicate(d) {
                to_remove.push(d.clone());
            }
        }
        for r in &to_remove {
            self.remove_refed(r);
        }
        !to_remove.is_empty()
    }

    // pub fn remove_depend_on_that(&self, predicate: impl Fn(&IRRef) -> bool) -> bool {
    //     let mut r = false;
    //     for d in self.borrow().depend_on.borrow().iter() {
    //         if d.is_empty() {
    //             self.remove_depend_on(d);
    //             continue;
    //         }
    //         let p = predicate(&d.clone().into());
    //         if p {
    //             let tmp1 = Weak::upgrade(&d.ir).unwrap();
    //             let tmp2 = RefCell::borrow(&tmp1);
    //             // assert!(tmp2.value_ref().is_none() || !self.borrow().operands().contains(&tmp2.value_ref().unwrap()));
    //             self.remove_depend_on(d);
    //             r = true;
    //         }
    //     }
    //     r
    // }

    pub fn add_refed(&self, to_add: MutableIRRef) {
        RefCell::borrow_mut(&self.borrow().refed_by).insert(to_add.clone());
        RefCell::borrow_mut(&to_add.borrow().depend_on).insert(self.clone().into());
    }

    pub fn add_refed_all(&self, to_add: impl Iterator<Item = MutableIRRef>) {
        for ir in to_add {
            self.add_refed(ir);
        }
    }

    pub fn replace_refed(&self, old: MutableIRRef, new: MutableIRRef) {
        self.remove_refed(&old);
        self.add_refed(new);
    }
}
