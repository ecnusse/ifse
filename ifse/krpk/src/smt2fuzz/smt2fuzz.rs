use std::borrow::{Borrow, BorrowMut};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use std::rc::Rc;

use either::Either;
use itertools::Itertools;

use crate::mir::{
    DeclaredCBFunction, DeclaredConstant, FuzzProgram, IRKind, IRRef, LiteralValue, MutableIRRef,
    Type, ValueRef, IR,
};
use crate::smtanalyze::{
    KRPKEnvironment, KRPKFunction, KRPKFunctionDeclaration, KRPKGroundSort, KRPKIdentifier,
    KRPKIndex, KRPKMatchCase, KRPKQualIdentifier, KRPKSpecConstant, KRPKTerm, Sorted,
};

#[derive(Debug, Clone, PartialEq)]
pub enum SMT2FuzzError {
    UnsupportedSort(KRPKGroundSort),
    UnboundArray(KRPKFunctionDeclaration),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SMT2FuzzOpt {
    EquivClassMerge,
    // DeadCodeElimination,
}

/// [`SMT2Fuzz`] compiles HIR (an AST) to MIR (SSA instructions) and perform low-level optimizations on MIR.
#[derive(Clone)]
pub struct SMT2Fuzz {
    optimizations: Vec<Rc<dyn Fn(FuzzProgram) -> Result<FuzzProgram, SMT2FuzzError>>>,
}

impl Default for SMT2Fuzz {
    fn default() -> Self {
        Self::new()
    }
}

impl SMT2Fuzz {
    pub fn new() -> Self {
        Self::with_opts(&[SMT2FuzzOpt::EquivClassMerge])
    }

    /// Create an smt2fuzz with no optimizations.
    pub fn no_opt() -> Self {
        Self {
            optimizations: vec![],
        }
    }

    pub fn with_opts(opts: &[SMT2FuzzOpt]) -> Self {
        let mut optimizations: Vec<Rc<dyn Fn(FuzzProgram) -> Result<FuzzProgram, SMT2FuzzError>>> =
            vec![];
        let mut added = HashSet::new();
        for opt in opts {
            if added.contains(opt) {
                panic!("Duplicated optimization: {:?}", opt);
            }
            added.insert(opt);
            match opt {
                SMT2FuzzOpt::EquivClassMerge => {
                    optimizations.push(Rc::new(Self::merge_equiv_class));
                    optimizations.push(Rc::new(Self::merge_equiv_class_array));
                    optimizations.push(Rc::new(Self::remove_dead_entries))
                }
            }
        }
        Self { optimizations }
    }

    fn remove_dead_entries(program: FuzzProgram) -> Result<FuzzProgram, SMT2FuzzError> {
        let mut program = program;
        let sinks = RefCell::new(HashSet::new());
        program.visit(|ir| match ir.borrow().kind() {
            IRKind::Check | IRKind::Memset(..) | IRKind::WriteBack(..) => {
                sinks.borrow_mut().insert(ir.clone());
            }
            _ => {}
        });

        let mut used = HashSet::new();
        let mut work_list = VecDeque::from_iter(sinks.borrow().clone());
        while let Some(h) = work_list.pop_front() {
            if !used.insert(h.clone()) {
                continue;
            }
            for pred in h.borrow().operands() {
                work_list.push_back(pred.ir().clone().into());
            }
        }
        program.remove_entries_that(|e| !used.contains(e));
        Ok(program)
    }

    fn merge_equiv_class(program: FuzzProgram) -> Result<FuzzProgram, SMT2FuzzError> {
        let mut program = program;
        let equivalence: RefCell<HashMap<usize, (Rc<DeclaredConstant>, IRRef, ValueRef)>> =
            RefCell::new(HashMap::new());

        // Collect cb-func related equivalence
        program.visit(|ir| match ir.borrow().kind() {
            IRKind::Eq => {
                let mut assert_true = false;
                for s in ir.borrow().successors() {
                    if let IRKind::Check = s.borrow().kind() {
                        assert_true = true;
                        break;
                    }
                }
                if !assert_true {
                    return;
                }
                for (idx, operand) in ir.borrow().operands().iter().enumerate() {
                    assert!(idx == 0 || idx == 1);
                    let mut equiv = equivalence.borrow_mut();
                    match operand.ir().borrow().kind() {
                        IRKind::ConstantRef(c) => {
                            let ptr_v = Rc::as_ptr(c) as usize;
                            if equiv.contains_key(&ptr_v) {
                                continue;
                            }
                            if let IRKind::CallCBFunction(..) =
                                ir.borrow().operands()[1 - idx].ir().borrow().kind()
                            {
                            } else {
                                continue;
                            }
                            equiv.insert(
                                ptr_v,
                                (
                                    c.clone(),
                                    ir.clone(),
                                    ir.borrow().operands()[1 - idx].clone(),
                                ),
                            );
                            break;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        });

        // Collect other equivalence if there's no cb-func ones
        program.visit(|ir| match ir.borrow().kind() {
            IRKind::Eq => {
                let mut assert_true = false;
                for s in ir.borrow().successors() {
                    if let IRKind::Check = s.borrow().kind() {
                        assert_true = true;
                        break;
                    }
                }
                if !assert_true {
                    return;
                }
                for (idx, operand) in ir.borrow().operands().iter().enumerate() {
                    assert!(idx == 0 || idx == 1);
                    let mut equiv = equivalence.borrow_mut();
                    match operand.ir().borrow().kind() {
                        IRKind::ConstantRef(c) => {
                            let ptr_v = Rc::as_ptr(c) as usize;
                            if equiv.contains_key(&ptr_v) {
                                continue;
                            }
                            if let IRKind::Literal { .. } =
                                ir.borrow().operands()[1 - idx].ir().borrow().kind()
                            {
                            } else {
                                continue;
                            }
                            equiv.insert(
                                ptr_v,
                                (
                                    c.clone(),
                                    ir.clone(),
                                    ir.borrow().operands()[1 - idx].clone(),
                                ),
                            );
                            break;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        });

        let newly_added = RefCell::new(HashSet::new());
        
        // XXX: Don't know why but a single visit_mut is not enough. It will fail in certain test cases (and we don't know why).
        loop {
            let changed = Cell::new(false);
            program.visit_mut(|ir| {
                let IRKind::ConstantRef(c) = ir.borrow().kind().clone() else {
                    return;
                };
                let ptr_v = Rc::as_ptr(&c) as usize;
                let equiv = equivalence.borrow();
                let Some((_, used, equiv_term)) = equiv.get(&ptr_v) else {
                    return;
                };
                let alias = IR::new(IRKind::Alias, vec![equiv_term.clone()]);
                for succ in ir.borrow().successors() {
                    if succ == used.clone() {
                        continue;
                    }
                    changed.set(true);
                    let succ_mut: MutableIRRef = succ.clone().into();
                    succ_mut.rewire_to(
                        ir.borrow().value_ref().unwrap(),
                        alias.borrow().value_ref().unwrap(),
                    );
                    if let IRKind::Memset(..) = succ.borrow().kind() {
                        Self::break_loop(succ_mut.clone());
                    }
                }
            });
            if !changed.get() {
                break;
            }
        }
        let equiv = equivalence.borrow();
        for (_, (c, used, t)) in equiv.iter() {
            let _equiv_term = t.ir();
            c.set_virtual(0, c.size_in_bytes());

            let taut = IR::new(
                IRKind::Literal {
                    literal: LiteralValue::BoolValue(true),
                },
                Default::default(),
            );
            RefCell::borrow_mut(&newly_added).insert(taut.clone());
            for succ in used.borrow().successors() {
                let succ_mut: MutableIRRef = succ.clone().into();
                succ_mut.rewire_to(
                    used.borrow().value_ref().unwrap(),
                    taut.borrow().value_ref().unwrap(),
                );
            }
        }
        program.add_entires(newly_added.into_inner().into_iter());
        Ok(program)
    }

    fn break_loop(ir: MutableIRRef) {
        assert!(if let IRKind::Memset(..) = ir.borrow().kind() {
            true
        } else {
            false
        });
        let detect = |start: IRRef| -> bool {
            let mut visited = HashSet::new();
            let mut wl = VecDeque::new();
            wl.push_back(start);
            while let Some(current) = wl.pop_front() {
                if !visited.insert(current.clone()) {
                    continue;
                }
                if current == ir.clone().into() {
                    return true;
                }
                for succ in current.borrow().successors() {
                    wl.push_back(succ);
                }
            }
            false
        };
        let t = ir.borrow();
        let next = t.successors();
        let mut to_break = vec![];
        for n in next {
            if detect(n.clone()) {
                to_break.push(n);
            }
        }
        for n in to_break {
            ir.remove_refed(&n.into());
        }
    }

    // FIXME: The opt may encounter bugs when there's non-const array indices
    fn merge_equiv_class_array(program: FuzzProgram) -> Result<FuzzProgram, SMT2FuzzError> {
        let mut program = program;
        #[derive(Debug)]
        struct ArrayConcat(Rc<DeclaredConstant>, usize);

        impl PartialEq for ArrayConcat {
            fn eq(&self, other: &Self) -> bool {
                Rc::ptr_eq(&self.0, &other.0) && self.1 == other.1
            }
        }

        impl Hash for ArrayConcat {
            fn hash<H: Hasher>(&self, state: &mut H) {
                Rc::as_ptr(&self.0).hash(state);
                self.1.hash(state);
            }
        }

        impl Eq for ArrayConcat {}

        fn trace_array_concat(ir: &IRRef) -> Option<ArrayConcat> {
            fn bytes_to_usize(bytes: &[u8]) -> usize {
                assert!(bytes.len() <= 8);
                let mut value = 0usize;
                for byte in bytes.iter().rev() {
                    value <<= 8;
                    value |= *byte as usize;
                }
                value
            }
            match ir.borrow().kind() {
                IRKind::Select => {
                    let IRKind::Literal { literal } =
                        ir.borrow().operands()[1].ir().borrow().kind().clone()
                    else {
                        return None;
                    };
                    let LiteralValue::BitVecValue(sz, bytes) = literal else {
                        unreachable!()
                    };
                    assert_eq!(0, sz % 8);
                    let idx = bytes_to_usize(&bytes);
                    let IRKind::ConstantRef(array_constant) =
                        ir.borrow().operands()[0].ir().borrow().kind().clone()
                    else {
                        return None;
                    };
                    if idx == 0 {
                        Some(ArrayConcat(array_constant, idx))
                    } else {
                        None
                    }
                }
                IRKind::Concat => {
                    let Some(rhs) = trace_array_concat(&ir.borrow().operands()[1].ir().into())
                    else {
                        return None;
                    };
                    let lhs = ir.borrow().operands()[0].clone();
                    let IRKind::Literal { literal } =
                        lhs.ir().borrow().operands()[1].ir().borrow().kind().clone()
                    else {
                        return None;
                    };
                    let LiteralValue::BitVecValue(sz, bytes) = literal else {
                        unreachable!()
                    };
                    assert_eq!(0, sz % 8);
                    let idx = bytes_to_usize(&bytes);
                    let IRKind::ConstantRef(array_constant) =
                        lhs.ir().borrow().operands()[0].ir().borrow().kind().clone()
                    else {
                        return None;
                    };
                    if Rc::ptr_eq(&rhs.0, &array_constant) && idx == rhs.1 + 1 {
                        Some(ArrayConcat(array_constant, idx))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }

        let equivalence = RefCell::new(HashMap::new());

        // Collect cb-func related equivalence
        program.visit(|ir| match ir.borrow().kind() {
            IRKind::Eq => {
                let mut assert_true = false;
                for s in ir.borrow().successors() {
                    if let IRKind::Check = s.borrow().kind() {
                        assert_true = true;
                        break;
                    }
                }
                if !assert_true {
                    return;
                }
                for (idx, operand) in ir.borrow().operands().iter().enumerate() {
                    assert!(idx == 0 || idx == 1);
                    let Some(array_concat) = trace_array_concat(&operand.ir().into()) else {
                        continue;
                    };
                    if let IRKind::CallCBFunction(..) =
                        ir.borrow().operands()[1 - idx].ir().borrow().kind()
                    {
                    } else {
                        return;
                    }
                    let mut equiv = equivalence.borrow_mut();
                    let ptr_v = Rc::as_ptr(&array_concat.0) as usize;
                    if equiv.contains_key(&ptr_v) {
                        continue;
                    }
                    equiv.insert(
                        ptr_v,
                        (
                            array_concat,
                            ir.clone(),
                            ir.borrow().operands()[1 - idx].clone(),
                        ),
                    );
                    break;
                }
            }
            _ => {}
        });

        // Collect other equivalence if there's no cb-func ones
        program.visit(|ir| match ir.borrow().kind() {
            IRKind::Eq => {
                let mut assert_true = false;
                for s in ir.borrow().successors() {
                    if let IRKind::Check = s.borrow().kind() {
                        assert_true = true;
                        break;
                    }
                }
                if !assert_true {
                    return;
                }
                for (idx, operand) in ir.borrow().operands().iter().enumerate() {
                    assert!(idx == 0 || idx == 1);
                    let Some(array_concat) = trace_array_concat(&operand.ir().into()) else {
                        continue;
                    };
                    if let IRKind::Literal { .. } =
                        ir.borrow().operands()[1 - idx].ir().borrow().kind()
                    {
                    } else {
                        return;
                    }
                    let mut equiv = equivalence.borrow_mut();
                    let ptr_v = Rc::as_ptr(&array_concat.0) as usize;
                    if equiv.contains_key(&ptr_v) {
                        continue;
                    }
                    equiv.insert(
                        ptr_v,
                        (
                            array_concat,
                            ir.clone(),
                            ir.borrow().operands()[1 - idx].clone(),
                        ),
                    );
                    break;
                }
            }
            _ => {}
        });

        let newly_added = RefCell::new(HashSet::new());
        let has_been_changed = RefCell::new(HashSet::new());
        loop {
            let changed = Cell::new(false);
            program.visit_mut(|ir| {
                match ir.borrow().kind() {
                    IRKind::Concat | IRKind::Select => {}
                    _ => return,
                };
                // Ensure the largest array concat
                for succ in ir.borrow().successors() {
                    if let IRKind::Concat = succ.borrow().kind() {
                        return;
                    }
                }
                let Some(array_concat) = trace_array_concat(&ir.clone().into()) else {
                    return;
                };
                let ptr_v = Rc::as_ptr(&array_concat.0) as usize;
                let equiv = equivalence.borrow();
                let Some((stored, used, equiv_term)) = equiv.get(&ptr_v) else {
                    return;
                };
                if stored.1 == array_concat.1 {
                    let alias = IR::new(IRKind::Alias, vec![equiv_term.clone()]);
                    for succ in ir.borrow().successors() {
                        if succ == used.clone() {
                            continue;
                        }
                        changed.set(true);
                        let succ_mut: MutableIRRef = succ.clone().into();
                        succ_mut.rewire_to(
                            ir.borrow().value_ref().unwrap(),
                            alias.borrow().value_ref().unwrap(),
                        );
                        if let IRKind::Memset(..) = succ.borrow().kind() {
                            Self::break_loop(succ_mut.clone());
                        }
                    }
                } else if stored.1 > array_concat.1 {
                    if !has_been_changed.borrow_mut().insert(ir.clone()) {
                        return;
                    }
                    changed.set(true);
                    let segment = IR::new(
                        IRKind::Extract(
                            0,
                            (array_concat.1 + 1)
                                * stored.0.type_.bitvec_array_range_width().unwrap()
                                - 1,
                        ),
                        vec![equiv_term.clone()],
                    );
                    for succ in ir.borrow().successors() {
                        let succ_mut: MutableIRRef = succ.clone().into();
                        succ_mut.rewire_to(
                            ir.borrow().value_ref().unwrap(),
                            segment.clone().borrow().value_ref().unwrap(),
                        );
                        if let IRKind::Memset(..) = succ.borrow().kind() {
                            Self::break_loop(succ_mut.clone());
                        }
                    }
                } else {
                    changed.set(true);
                    let diff = array_concat.1 - stored.1;
                    let bound = {
                        let mut p: MutableIRRef = ir.clone();
                        for _ in 0..diff - 1 {
                            p = p.clone().borrow().operands()[1].ir();
                        }
                        p
                    };
                    let tmp = bound.clone().borrow().operands()[1].clone();
                    bound.rewire_to(tmp, equiv_term.clone());
                    for succ in bound.borrow().successors() {
                        let succ_mut: MutableIRRef = succ.clone().into();
                        if let IRKind::Memset(..) = succ.borrow().kind() {
                            Self::break_loop(succ_mut.clone());
                        }
                    }
                }
            });
            if !changed.get() {
                break;
            }
        }
        let equiv = equivalence.borrow();
        for (_ptr_v, (c, used, _t)) in equiv.iter() {
            c.0.set_virtual(0, c.1 + 1);

            let taut = IR::new(
                IRKind::Literal {
                    literal: LiteralValue::BoolValue(true),
                },
                Default::default(),
            );
            RefCell::borrow_mut(&newly_added).insert(taut.clone());
            for succ in used.borrow().successors() {
                let succ_mut: MutableIRRef = succ.clone().into();
                succ_mut.rewire_to(
                    used.borrow().value_ref().unwrap(),
                    taut.borrow().value_ref().unwrap(),
                );
            }
        }
        program.add_entires(newly_added.into_inner().into_iter());
        Ok(program)
    }

    /// Convert an SMT-LIB sort to a C type.
    /// Note that array index bounds keep untouched in this function and is set to `None` by default.
    /// Index bounds are queried from the [`KRPKEnvironment`] and inserted later.
    fn sort_to_type(sort: &KRPKGroundSort) -> Result<Type, SMT2FuzzError> {
        if sort.is_bool() {
            Ok(Type::Bool)
        } else if sort.is_bit_vec() {
            Ok(Type::BitVec(sort.bit_vec_width().unwrap()))
        } else if sort.is_array() {
            let domain = sort.array_domain().unwrap();
            let range = sort.array_range().unwrap();
            if !domain.is_bit_vec() || !range.is_bit_vec() {
                return Err(SMT2FuzzError::UnsupportedSort(sort.clone()));
            }
            Ok(Type::BitVecArray {
                domain_width: domain.bit_vec_width().unwrap(),
                range_width: range.bit_vec_width().unwrap(),
                upper_bound: None,
            })
        } else {
            unreachable!("Unsupported sort: {:?}", sort)
        }
    }

    /// Transform HIR to MIR by DFS on the AST without any optimization.
    fn smt2fuzz(&mut self, env: &KRPKEnvironment) -> Result<FuzzProgram, SMT2FuzzError> {
        let user_functions = env.user_functions();
        let mut unknowns: HashMap<KRPKIdentifier, Rc<DeclaredConstant>> = HashMap::new();
        let mut cb_functions: HashMap<KRPKIdentifier, Rc<DeclaredCBFunction>> = HashMap::new();
        for func in user_functions {
            match func {
                KRPKFunction::Predefined(_) => unreachable!(),
                KRPKFunction::DeclaredConstant(decl) => {
                    let KRPKIdentifier::Symbol(name) = &decl.id else {
                        unreachable!()
                    };
                    let sort = decl.map_sort(&[]).unwrap();
                    let mut type_ = Self::sort_to_type(&sort)?;
                    match type_.clone() {
                        Type::BitVecArray {
                            domain_width,
                            range_width,
                            upper_bound: index_bound,
                        } => {
                            assert!(index_bound.is_none());
                            let index_bound = env.get_array_index_bound(&decl.id);
                            if let Some(index_bound) = index_bound {
                                type_ = Type::BitVecArray {
                                    domain_width,
                                    range_width,
                                    upper_bound: Some(index_bound),
                                };
                            } else {
                                return Err(SMT2FuzzError::UnboundArray(decl.clone()));
                            }
                        }
                        _ => {}
                    }
                    let declared_constant = DeclaredConstant::new(name.clone(), type_);
                    unknowns.insert(decl.id.clone(), Rc::new(declared_constant));
                }
                KRPKFunction::CBFunction(krpk_decl) => {
                    let decl = DeclaredCBFunction {
                        id: match &krpk_decl.id {
                            KRPKIdentifier::Symbol(name) => name.clone(),
                            _ => unreachable!(),
                        },
                        params: krpk_decl
                            .params
                            .clone()
                            .iter()
                            .map(|(st, ct)| {
                                let type_ = Self::sort_to_type(st).unwrap();
                                (type_, ct.clone())
                            })
                            .collect(),
                        return_smt_and_c_type: (
                            Self::sort_to_type(&krpk_decl.return_sort_and_type.0)?,
                            krpk_decl.return_sort_and_type.1.clone(),
                        ),
                    };
                    cb_functions.insert(krpk_decl.id.clone(), Rc::new(decl.clone()));
                }
            }
        }

        let ctypes = env.ctypes();
        let mut ctype_smt_correspondence = HashMap::new();
        for (ctype, sort) in ctypes {
            let type_ = Self::sort_to_type(sort)?;
            ctype_smt_correspondence.insert(ctype.to_string(), type_);
        }

        fn visit(
            term: &Sorted<KRPKTerm>,
            pre_action: &mut dyn FnMut(&Sorted<KRPKTerm>),
            post_action: &mut dyn FnMut(&Sorted<KRPKTerm>) -> MutableIRRef,
        ) -> MutableIRRef {
            use KRPKTerm::*;
            pre_action(term);
            match term.inner() {
                SpecConstant(_) | Identifier(_) => {}
                KRPKTerm::Let(bindings, inner) => {
                    for (_, term) in bindings {
                        visit(term, pre_action, post_action);
                    }
                    visit(&inner.clone().map_inner(|e| *e), pre_action, post_action);
                }
                KRPKTerm::Forall(_, inner) => {
                    visit(&inner.clone().map_inner(|e| *e), pre_action, post_action);
                }
                KRPKTerm::Exists(_, inner) => {
                    visit(&inner.clone().map_inner(|e| *e), pre_action, post_action);
                }
                KRPKTerm::Match(term, match_cases) => {
                    visit(&term.clone().map_inner(|e| *e), pre_action, post_action);
                    for mc in match_cases {
                        let KRPKMatchCase {
                            body: body_term, ..
                        } = mc.inner();
                        visit(body_term, pre_action, post_action);
                    }
                }
                KRPKTerm::Apply(_, args) => {
                    for arg in args {
                        visit(arg, pre_action, post_action);
                    }
                }
            }
            post_action(term)
        }

        let assertions = env.assertions();

        let mut pre_action = |_term: &Sorted<KRPKTerm>| {};

        let term_to_ir: RefCell<HashMap<Sorted<KRPKTerm>, MutableIRRef>> = Default::default();
        let entry_points: RefCell<HashSet<MutableIRRef>> = Default::default();

        let mut post_action = |term: &Sorted<KRPKTerm>| -> MutableIRRef {
            match term.inner() {
                KRPKTerm::Apply(id, args) => {
                    let mut arg_refs: Vec<_> = args
                        .iter()
                        .map(|arg| RefCell::borrow(&term_to_ir).get(arg).unwrap().clone())
                        .collect();
                    {
                        let (id, sort) = match id {
                            KRPKQualIdentifier::Qualified(id, sort) => (id, Some(sort)),
                            KRPKQualIdentifier::Simple(id) => (id, None),
                        };
                        let func = env.lookup_function(id).unwrap();
                        match func {
                            KRPKFunction::CBFunction(_) => {
                                let cb_function = cb_functions.get(id).unwrap().clone();
                                let kind = IRKind::CallCBFunction(cb_function);
                                let ir = IR::new(
                                    kind,
                                    arg_refs
                                        .iter()
                                        .map(|r| r.borrow().value_ref().unwrap())
                                        .collect_vec(),
                                );
                                RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                ir
                            }
                            KRPKFunction::DeclaredConstant(_) => unreachable!(),
                            KRPKFunction::Predefined(_decl) => {
                                let (id, indices) = match id {
                                    KRPKIdentifier::Symbol(id1) => (id1.clone(), None),
                                    KRPKIdentifier::Indexed(id1, indices) => {
                                        (id1.clone(), Some(indices.clone()))
                                    }
                                };

                                // use IRKind::*;
                                match_template! {
                                    SIMPLE = ["not" => Not, "bvnot" => BVNot, "bvneg" => BVNeg, "bv2bool" => BV2Bool, "bool2bv" => Bool2BV,
                                             "concat" => Concat, "bvudiv" => BVUDiv, "bvurem" => BVURem, "bvshl" => BVShL,
                                             "bvlshr" => BVLShR, "bvult" => BVULt,   "bvcomp" => BVComp , "bvsub" => BVSub,
                                             "bvsdiv" => BVSDiv, "bvsrem" => BVSRem, "bvsmod" => BVSMod, "bvashr" => BVAShR,
                                             "bvule" => BVULe,   "bvugt" => BVUGt,   "bvuge" => BVUGe,   "bvslt" => BVSLt,
                                             "bvsle" => BVSLe,   "bvsgt" => BVSGt,   "bvsge" => BVSGe,   "select" => Select, "store" => Store, "ite" => Ite],

                                    LEFT_ASSOC = ["and"  => And,  "or" => Or,       "bvand" => BVAnd,
                                                  "bvor" => BVOr, "bvadd" => BVAdd, "bvmul" => BVMul],

                                    NOT_COMPOUND_LOGIC = ["bvnand" => BVAnd, "bvnor" => BVOr],

                                    BIT_EXT = ["repeat" => Repeat, "zero_extend" => ZeroExtend, "sign_extend" => SignExtend,
                                               "rotate_left" => RotateLeft, "rotate_right" => RotateRight],

                                    match id.as_str() {
                                        SIMPLE => {
                                            let kind = IRKind::SIMPLE;
                                            let ir = IR::new(kind, arg_refs.iter().map(|r| r.borrow().value_ref().unwrap()).collect_vec());
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        }

                                        LEFT_ASSOC => {
                                            let mut current = arg_refs.pop().unwrap();
                                            while let Some(arg) = arg_refs.pop() {
                                                current = {
                                                    let kind = IRKind::LEFT_ASSOC;
                                                    IR::new(kind, vec![arg.borrow().value_ref().unwrap(), current.clone().borrow().value_ref().unwrap()])
                                                }
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },

                                        NOT_COMPOUND_LOGIC => {
                                            let mut current = arg_refs.pop().unwrap(); // current is b because of STACK LIFO property.
                                            while let Some(arg) = arg_refs.pop() {
                                                current = {
                                                    let kind = IRKind::NOT_COMPOUND_LOGIC;
                                                    IR::new(kind, vec![arg.borrow().value_ref().unwrap(), current.clone().borrow().value_ref().unwrap()])
                                                }
                                            }
                                            let ir = IR::new(IRKind::BVNot, vec![current.borrow().value_ref().unwrap()]);
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        },

                                        BIT_EXT => {
                                            let bit_count = match indices.unwrap().as_slice() {
                                                [KRPKIndex::Numeral(times)] => *times,
                                                _ => unreachable!(),
                                            };
                                            let kind = IRKind::BIT_EXT(bit_count);
                                            let ir = IR::new(kind, arg_refs.iter().map(|r| r.borrow().value_ref().unwrap()).collect_vec());
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        },
                                        "ensure_index" => {
                                            let kind = IRKind::Literal {literal: LiteralValue::BoolValue(true)};
                                            let ir = IR::new(kind, vec![]);
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        }
                                        // Special case: equal
                                        "=" => {
                                            let mut collected = vec![];
                                            let arg_refs1 = arg_refs.clone();
                                            for (e1, e2) in arg_refs.iter().zip(arg_refs1[1..].into_iter()) {
                                                let tmp = IR::new(IRKind::Eq, vec![e1.borrow().value_ref().unwrap(), e2.borrow().value_ref().unwrap()]);
                                                collected.push(tmp);
                                            }
                                            let mut current = collected.pop().unwrap();
                                            while let Some(arg) = collected.pop() {
                                                current = {
                                                    IR::new(IRKind::And, vec![arg.borrow().value_ref().unwrap(), current.clone().borrow().value_ref().unwrap()])
                                                }
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },
                                        // Special case: distinct
                                        "distinct" => {
                                            let mut collected_refs = Vec::new();
                                            for (arg1, arg2) in
                                                arg_refs.iter().cartesian_product(arg_refs.iter().collect_vec())
                                            {
                                                if arg1 != arg2 {
                                                    collected_refs.push(IR::new(IRKind::Ne, vec![arg1.borrow().value_ref().unwrap(), arg2.borrow().value_ref().unwrap()]));
                                                }
                                            }
                                            let mut current = collected_refs.pop().unwrap();
                                            while let Some(arg) = collected_refs.pop() {
                                                current = {
                                                    IR::new(IRKind::And, vec![arg.borrow().value_ref().unwrap(), current.clone().borrow().value_ref().unwrap()])
                                                }
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },
                                        // Special case: imply
                                        "=>" => {
                                            let left = arg_refs[0].clone();
                                            let right = arg_refs[1].clone();
                                            let ir = IR::new(IRKind::Or, vec![IR::new(IRKind::Not, vec![left.borrow().value_ref().unwrap()]).borrow().value_ref().unwrap(), right.borrow().value_ref().unwrap()]);
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        },
                                        // Special case: xor
                                        "xor" => {
                                            let xor = |left: MutableIRRef, right: MutableIRRef| {
                                                let first_clause = {
                                                    IR::new(IRKind::And, vec![IR::new(IRKind::Not, vec![left.borrow().value_ref().unwrap()]).borrow().value_ref().unwrap(), right.borrow().value_ref().unwrap()])
                                                }.borrow().value_ref().unwrap();
                                                let second_clause = {
                                                    IR::new(IRKind::And, vec![left.borrow().value_ref().unwrap(), IR::new(IRKind::Not, vec![right.borrow().value_ref().unwrap()]).borrow().value_ref().unwrap()])
                                                }.borrow().value_ref().unwrap();
                                                IR::new(IRKind::Or, vec![first_clause, second_clause])
                                            };
                                            let mut arg_refs = arg_refs.clone();
                                            let mut current = arg_refs.pop().unwrap();
                                            while let Some(arg) = arg_refs.pop() {
                                                current = xor(arg, current.clone());
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },
                                        // Special case: bvxor
                                        "bvxor" => {
                                            let bvxor = |left: MutableIRRef, right: MutableIRRef| {
                                                let nleft = IR::new(IRKind::BVNot, vec![left.borrow().value_ref().unwrap()]);
                                                let nleft_ref = nleft.borrow().value_ref().unwrap();
                                                let nright = IR::new(IRKind::BVNot, vec![right.borrow().value_ref().unwrap()]);
                                                let nright_ref = nright.borrow().value_ref().unwrap();
                                                let first_clause =
                                                    IR::new(IRKind::BVAnd, vec![nleft_ref, right.borrow().value_ref().unwrap()]);
                                                let second_clause =
                                                    IR::new(IRKind::BVAnd, vec![left.borrow().value_ref().unwrap(), nright_ref]);
                                                let ref1 = first_clause.borrow().value_ref().unwrap();
                                                let ref2 = second_clause.borrow().value_ref().unwrap();
                                                IR::new(IRKind::BVOr, vec![ref1, ref2])
                                            };
                                            // xor a b = (and (not a) b) or (and a (not b))
                                            let mut arg_refs = arg_refs.clone();
                                            let mut current = arg_refs.pop().unwrap(); // Now current is b
                                            while let Some(arg) = arg_refs.pop() {
                                                current = bvxor(arg, current.clone());
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },
                                        // Special case: bvxnor a b = (a and b) or ((not a) and (not b))
                                        "bvxnor" => {
                                            let bvxnor = |_left: MutableIRRef, _right: MutableIRRef| {
                                                let first_clause = {
                                                    let left = arg_refs[0].clone().borrow().value_ref().unwrap();
                                                    let right = arg_refs[1].clone().borrow().value_ref().unwrap();
                                                    IR::new(IRKind::And, vec![left, right])
                                                }.borrow().value_ref().unwrap();
                                                let second_clause = {
                                                    let left = arg_refs[0].clone().borrow().value_ref().unwrap();
                                                    let right = arg_refs[1].clone().borrow().value_ref().unwrap();
                                                    IR::new(IRKind::And, vec![IR::new(IRKind::BVNot, vec![left]).borrow().value_ref().unwrap(), IR::new(IRKind::BVNot, vec![right]).borrow().value_ref().unwrap()])
                                                }.borrow().value_ref().unwrap();
                                                IR::new(IRKind::Or, vec![first_clause, second_clause])
                                            };
                                            // xnor a b = (a and b) or ((not a) and (not b))
                                            // however, (xnor a b) is equal to (xnor b a)
                                            let mut arg_refs = arg_refs.clone();
                                            let mut current = arg_refs.pop().unwrap(); // current is b
                                            while let Some(arg) = arg_refs.pop() {
                                                current = bvxnor(arg, current.clone());
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        },
                                        // Special case: extract
                                        "extract" => {
                                            // from low to high
                                            let (to, from) = match indices.unwrap().as_slice() {
                                                [KRPKIndex::Numeral(to), KRPKIndex::Numeral(from)] => {
                                                    (*to, *from)
                                                }
                                                _ => unreachable!(),
                                            };
                                            let ir = IR::new(IRKind::Extract(from, to), arg_refs.iter().map(|r| r.borrow().value_ref().unwrap()).collect_vec());
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        },
                                        // Special case: const
                                        "const" => {
                                            let array_sort = sort.unwrap();
                                            let domain_bits = array_sort
                                                .array_domain()
                                                .unwrap()
                                                .bit_vec_width()
                                                .unwrap();
                                            let range_bits = array_sort
                                                .array_range()
                                                .unwrap()
                                                .bit_vec_width()
                                                .unwrap();
                                            let ir = IR::new(IRKind::ConstBVArray(domain_bits, range_bits), arg_refs.iter().map(|r| r.borrow().value_ref().unwrap()).collect_vec());
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                                            ir
                                        },
                                        "god_save_me_const" => {
                                            let array_sort = sort.unwrap();
                                            let domain_bits = array_sort
                                                .array_domain()
                                                .unwrap()
                                                .bit_vec_width()
                                                .unwrap();
                                            let range_bits = array_sort
                                                .array_range()
                                                .unwrap()
                                                .bit_vec_width()
                                                .unwrap();
                                            let mut current = IR::new(IRKind::ConstBVArray(domain_bits, range_bits), arg_refs.iter().map(|r| r.borrow().value_ref().unwrap()).collect_vec());
                                            let KRPKIndex::Symbol(hex) = indices.unwrap()[0].clone() else {
                                                unreachable!();
                                            };
                                            assert_eq!(32, domain_bits);
                                            assert_eq!(8, range_bits);
                                            assert_eq!(0, hex.len() % 2);
                                            for i in 0..hex.len() / 2 {
                                                let index = IR::new(
                                                    IRKind::Literal {
                                                        literal: LiteralValue::BitVecValue(
                                                            32, 
                                                            vec![
                                                                (i & 0xFF) as u8,
                                                                ((i & 0xFF00) >> 8) as u8, 
                                                                ((i & 0xFF0000) >> 16) as u8,
                                                                ((i & 0xFF000000) >> 24) as u8,
                                                            ]
                                                        )
                                                    }, 
                                                    vec![]
                                                );
                                                let byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).unwrap();
                                                let kind = IRKind::Literal {
                                                    literal: LiteralValue::BitVecValue(
                                                        8,
                                                        vec![byte],
                                                    ),
                                                };
                                                let value = IR::new(kind, Default::default());

                                                RefCell::borrow_mut(&entry_points).insert(index.clone());
                                                RefCell::borrow_mut(&entry_points).insert(value.clone());

                                                current = IR::new(
                                                    IRKind::Store, 
                                                    vec![current.clone().borrow().value_ref().unwrap(), index.borrow().value_ref().unwrap(), value.borrow().value_ref().unwrap()]
                                                );
                                            }
                                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), current.clone());
                                            current
                                        }
                                        _ => {
                                            unimplemented!()
                                        }
                                    }
                                }
                                // ***************************************************************************
                                // REFERENCE:
                                //      [SMT-LIB Standard](https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml)
                                //      [Microsoft Z3 Doc](https://microsoft.github.io/z3guide/docs/theories/Bitvectors)
                                // Word operations
                                // which can be found in [Microsoft Z3 Doc](https://microsoft.github.io/z3guide/docs/theories/Bitvectors)
                                // The above are about [Bitvector Theory](https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml),
                                // The below are about [Array](https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml)
                                // ***************************************************************************
                            }
                        }
                    }
                }
                KRPKTerm::SpecConstant(c) => {
                    let ir = match c {
                        KRPKSpecConstant::Hexadecimal(hex) => {
                            let kind = IRKind::Literal {
                                literal: LiteralValue::BitVecValue(
                                    hex.bit_num(),
                                    hex.bytes.clone(),
                                ),
                            };
                            IR::new(kind, Default::default())
                        }
                        KRPKSpecConstant::Binary(bin) => {
                            let kind = IRKind::Literal {
                                literal: LiteralValue::BitVecValue(
                                    bin.bit_num(),
                                    bin.bytes.clone(),
                                ),
                            };
                            IR::new(kind, Default::default())
                        }
                        _ => todo!(),
                    };
                    RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                    RefCell::borrow_mut(&entry_points).insert(ir.clone());
                    ir
                }
                KRPKTerm::Identifier(id) => {
                    let id = match id {
                        KRPKQualIdentifier::Qualified(id, _) => id,
                        KRPKQualIdentifier::Simple(id) => id,
                    };
                    let func = env.lookup_function(id).unwrap();
                    match func {
                        KRPKFunction::DeclaredConstant(_decl) => {
                            let declared_constant = unknowns.get(id).unwrap().clone();
                            let kind = IRKind::ConstantRef(declared_constant.clone());
                            let ir = IR::new(kind, Default::default());
                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                            RefCell::borrow_mut(&entry_points).insert(ir.clone());
                            ir
                        }
                        KRPKFunction::Predefined(_decl) => {
                            let id = match id {
                                KRPKIdentifier::Symbol(id) => id,
                                _ => unreachable!(),
                            };
                            let ir = match id.as_str() {
                                "true" => {
                                    let kind = IRKind::Literal {
                                        literal: LiteralValue::BoolValue(true),
                                    };
                                    IR::new(kind, Default::default())
                                }
                                "false" => {
                                    let kind = IRKind::Literal {
                                        literal: LiteralValue::BoolValue(false),
                                    };
                                    IR::new(kind, Default::default())
                                }
                                _ => todo!(),
                            };
                            RefCell::borrow_mut(&term_to_ir).insert(term.clone(), ir.clone());
                            RefCell::borrow_mut(&entry_points).insert(ir.clone());
                            ir
                        }
                        KRPKFunction::CBFunction(_) => todo!(),
                    }
                }
                KRPKTerm::Let(_, _) => todo!(),
                KRPKTerm::Forall(_, _) => todo!(),
                KRPKTerm::Exists(_, _) => todo!(),
                KRPKTerm::Match(_, _) => todo!(),
            }
        };
        // visit(term, pre_action, post_action)
        for assertion in assertions {
            let to_check = visit(assertion, &mut pre_action, &mut post_action);
            IR::new(IRKind::Check, vec![to_check.borrow().value_ref().unwrap()]);
        }

        let mut newly_added = vec![];
        for (_, unknown) in &unknowns {
            let cref = IR::new(IRKind::ConstantRef(unknown.clone()), vec![]);
            newly_added.push(cref.clone());
            RefCell::borrow_mut(&entry_points).insert(cref.clone());
            let wb = match &unknown.type_ {
                Type::BitVec(_) => {
                    let kind = IRKind::WriteBack(unknown.clone());
                    IR::new(kind, vec![cref.borrow().value_ref().unwrap()])
                }
                Type::BitVecArray {
                    domain_width,
                    range_width: _,
                    upper_bound,
                } => {
                    let ub = upper_bound.clone().unwrap();
                    let mut current: Option<MutableIRRef> = None;
                    for i in 0..=ub as u64 {
                        let e = {
                            fn u64_to_bytes(num: u64, bit_num: usize) -> Vec<u8> {
                                let mut bytes = vec![0u8; bit_num / 8 + 1];
                                for i in 0..bit_num / 8 + 1 {
                                    bytes[i] = (num >> (i * 8)) as u8;
                                }
                                bytes
                            }
                            let idx = {
                                let bytes = u64_to_bytes(i, *domain_width);
                                let literal = LiteralValue::BitVecValue(*domain_width, bytes);
                                let kind = IRKind::Literal { literal };
                                IR::new(kind, vec![])
                            };
                            RefCell::borrow_mut(&entry_points).insert(idx.clone());
                            newly_added.push(idx.clone());
                            let select = {
                                let kind = IRKind::Select;
                                IR::new(
                                    kind,
                                    vec![
                                        cref.borrow().value_ref().unwrap(),
                                        idx.borrow().value_ref().unwrap(),
                                    ],
                                )
                            };
                            newly_added.push(select.clone());
                            if let Some(before) = current.clone() {
                                let kind = IRKind::Concat;
                                IR::new(
                                    kind,
                                    vec![
                                        select.borrow().value_ref().unwrap(),
                                        before.borrow().value_ref().unwrap(),
                                    ],
                                )
                            } else {
                                select
                            }
                        };
                        newly_added.push(e.clone());
                        current = Some(e);
                    }
                    let bv = current.unwrap();
                    IR::new(
                        IRKind::WriteBack(unknown.clone()),
                        vec![bv.clone().borrow().value_ref().unwrap()],
                    )
                }
                Type::Bool => {
                    let kind = IRKind::WriteBack(unknown.clone());
                    IR::new(kind, vec![cref.borrow().value_ref().unwrap()])
                }
            };
            newly_added.push(wb);
        }

        let all_irs = {
            let tmp = RefCell::borrow(&term_to_ir);
            let mut tmp = tmp.values().cloned().collect::<HashSet<_>>();
            tmp.extend(newly_added);
            let tmp2 = RefCell::borrow(&entry_points);
            let tmp = tmp.difference(&tmp2);
            tmp.cloned().collect::<HashSet<_>>()
        };
        let mut mem_info = None;
        if let Some(_size) = env.memory_segment_size() {
            let mut min_addr = 0u64;
            let mut max_addr = 0u64;
            for (addr, sz, bytes) in env.memory_allocs() {
                min_addr = min_addr.min(*addr);
                max_addr = max_addr.max(*addr + (*sz as u64));
                match bytes {
                    Either::Left(term) => {
                        let r = visit(term, &mut pre_action, &mut post_action);
                        let kind = IRKind::Memset(*addr, None);
                        let ir = IR::new(kind, vec![r.borrow().value_ref().unwrap()]);
                        ir.add_refed_all(all_irs.iter().cloned());
                    }
                    Either::Right(byteLiteral) => {
                        let kind = IRKind::Memset(*addr, Some(byteLiteral.clone()));
                        let ir = IR::new(kind, Default::default());
                        ir.add_refed_all(all_irs.iter().cloned());
                        entry_points.borrow_mut().insert(ir.clone());
                    }
                }
            }
            mem_info = Some((min_addr, max_addr - min_addr));
        }
        let tmp = RefCell::borrow(&entry_points).clone();
        Ok(FuzzProgram::new(
            unknowns,
            mem_info,
            cb_functions,
            ctype_smt_correspondence,
            tmp,
        ))
    }

    /// Compile the SMT-LIB program into an SSA-form `FuzzProgram` and perform in sequence optimizations present in `self.optimizations`.
    pub fn compile(&mut self, env: &KRPKEnvironment) -> Result<FuzzProgram, SMT2FuzzError> {
        let mut program = self.smt2fuzz(env)?;
        for optimization in &self.optimizations {
            program = optimization(program)?;
        }
        Ok(program)
    }
}

// FIXME: Fix inconsistencies after change the output format of fuzz.cpp
#[cfg(test)]
mod test {
    use trim_margin::MarginTrimmable;

    use crate::{smtanalyze::Analyzer, smtparser::parse_str};

    use super::*;

    #[test]
    fn test_simple() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            | (set-logic ALL)
            | (declare-const x Bool)
            | (assert (= x true))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            &r#"
            |declare-const x Bool
            |expr_0 = x
            |expr_1 = true
            |expr_2 = eq expr_0 expr_1
            |cktrue expr_2
            |expr_3 = x
            |writeback x expr_3
        "#
            .trim_margin()
            .unwrap(),
            &tmp.trim()
        );
    }

    #[test]
    fn test_memset() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            | (set-logic ALL)
            | (set-arch X86)
            | (declare-const x Bool)
            | (define-ctype bool Bool)
            | (define-ctype bool* (_ BitVec 32))
            | (declare-cb test (bool*) bool)
            | (alloc #x00000000 1 x)
            | (assert (= true (test #x00000000)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            &r#"
            |memory-proxy mem_proxy_0_1<0, 1>
            |declare-const x Bool
            |declare-cb test (bool*/BitVec<32>) -> bool/Bool
            |expr_0 = true
            |expr_1 = bvx32#00000000
            |expr_4 = x
            |expr_5 = x
            |memset 0 expr_5
            |expr_2 = (test expr_1)
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
            |writeback x expr_4
        "#
            .trim_margin()
            .unwrap(),
            &tmp.trim()
        );
    }

    #[test]
    fn test_eq_chain() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const x Bool)
            |(declare-const y Bool)
            |(declare-const z Bool)
            |(assert (= x y z))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            &r#"
            |declare-const x Bool
            |declare-const y Bool
            |declare-const z Bool
            |expr_0 = x
            |expr_1 = y
            |expr_2 = z
            |expr_3 = eq expr_0 expr_1
            |expr_4 = eq expr_1 expr_2
            |expr_5 = and expr_3 expr_4
            |cktrue expr_5
            |expr_6 = z
            |writeback z expr_6
            |expr_7 = y
            |writeback y expr_7
            |expr_8 = x
            |writeback x expr_8
        "#
            .trim_margin()
            .unwrap(),
            &tmp.trim()
        );
    }

    #[test]
    fn test_bv_xor() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const w (_ BitVec 8))
            |(declare-const x (_ BitVec 8))
            |(declare-const y (_ BitVec 8))
            |(declare-const z (_ BitVec 8))
            |(assert (= (bvxor w x y z) #x00))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const w BitVec<8>
            |declare-const x BitVec<8>
            |declare-const y BitVec<8>
            |declare-const z BitVec<8>
            |expr_0 = w
            |expr_1 = x
            |expr_2 = y
            |expr_3 = z
            |expr_4 = bvnot expr_2
            |expr_5 = bvnot expr_3
            |expr_6 = bvand expr_4 expr_3
            |expr_7 = bvand expr_2 expr_5
            |expr_8 = bvor expr_6 expr_7
            |expr_9 = bvnot expr_1
            |expr_10 = bvnot expr_8
            |expr_11 = bvand expr_9 expr_8
            |expr_12 = bvand expr_1 expr_10
            |expr_13 = bvor expr_11 expr_12
            |expr_14 = bvnot expr_0
            |expr_15 = bvnot expr_13
            |expr_16 = bvand expr_14 expr_13
            |expr_17 = bvand expr_0 expr_15
            |expr_18 = bvor expr_16 expr_17
            |expr_19 = bvx8#00
            |expr_20 = eq expr_18 expr_19
            |cktrue expr_20
            expr_21 = w
            writeback w expr_21
            expr_22 = x
            writeback x expr_22
            expr_23 = y
            writeback y expr_23
            expr_24 = z
            writeback z expr_24

            declare-const w BitVec<8>
            declare-const x BitVec<8>
            declare-const y BitVec<8>
            declare-const z BitVec<8>
            expr_0 = w
            expr_1 = x
            expr_2 = y
            expr_3 = z
            expr_4 = bvnot expr_2
            expr_5 = bvnot expr_3
            expr_6 = bvand expr_4 expr_3
            expr_7 = bvand expr_2 expr_5
            expr_8 = bvor expr_6 expr_7
            expr_9 = bvnot expr_1
            expr_10 = bvnot expr_8
            expr_11 = bvand expr_9 expr_8
            expr_12 = bvand expr_1 expr_10
            expr_13 = bvor expr_11 expr_12
            expr_14 = bvnot expr_0
            expr_15 = bvnot expr_13
            expr_16 = bvand expr_14 expr_13
            expr_17 = bvand expr_0 expr_15
            expr_18 = bvor expr_16 expr_17
            expr_19 = bvx8#00
            expr_20 = eq expr_18 expr_19
            cktrue expr_20
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_arr_select() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const arr (Array (_ BitVec 8) (_ BitVec 8)))
            |(assert (= (select arr #x00) #x00))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const arr BitVecArray<8, 8, 0>
            |expr_0 = arr
            |expr_1 = bvx8#00
            |expr_2 = select expr_0 expr_1
            |expr_3 = bvx8#00
            |expr_4 = eq expr_2 expr_3
            |cktrue expr_4
            |expr_5 = arr
            |expr_6 = bvx8#0000
            |expr_7 = select expr_5 expr_6
            |writeback arr expr_7
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_arr_const() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) #x00) #x00))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |expr_0 = bvx8#01
            |expr_1 = constbva 8 8 expr_0
            |expr_2 = bvx8#00
            |expr_3 = select expr_1 expr_2
            |expr_4 = bvx8#00
            |expr_5 = eq expr_3 expr_4
            |cktrue expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_not() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = eq expr_0 expr_1
            |expr_3 = not expr_2
            |cktrue expr_3
            |expr_4 = b
            |writeback b expr_4
            |expr_5 = a
            |writeback a expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_imply() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = not expr_0
            |expr_3 = or expr_2 expr_1
            |cktrue expr_3
            |expr_4 = b
            |writeback b expr_4
            |expr_5 = a
            |writeback a expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_and() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = and expr_0 expr_1
            |cktrue expr_2
            |expr_3 = a
            |writeback a expr_3
            |expr_4 = b
            |writeback b expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_or() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = or expr_0 expr_1
            |cktrue expr_2
            |expr_3 = b
            |writeback b expr_3
            |expr_4 = a
            |writeback a expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_xor() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = not expr_0
            |expr_3 = and expr_2 expr_1
            |expr_4 = not expr_1
            |expr_5 = and expr_0 expr_4
            |expr_6 = or expr_3 expr_5
            |cktrue expr_6
            |expr_7 = a
            |writeback a expr_7
            |expr_8 = b
            |writeback b expr_8
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_equal() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = eq expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_distinct() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b Bool
            |expr_0 = a
            |expr_1 = b
            |expr_2 = ne expr_0 expr_1
            |expr_3 = ne expr_1 expr_0
            |expr_4 = and expr_2 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_ite() {
        crate::mir::reset_ref_id_count();
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
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a Bool
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = bvx8#01
            |expr_3 = bvx8#00
            |expr_4 = ite expr_1 expr_2 expr_3
            |expr_5 = eq expr_0 expr_4
            |cktrue expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_concat() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_BitVec 4))
            |(declare-const b (_BitVec 4))
            |(declare-const c (_BitVec 8))
            |(assert (= c (concat a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<4>
            |declare-const b BitVec<4>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = concat expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvnot() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (= b (bvnot a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = bvnot expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvand() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvand a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvand expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvor() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvor a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvor expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvneg() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (= b (bvneg a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = bvneg expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvadd() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvadd a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvadd expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvmul() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvmul a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvmul expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvudiv() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvudiv a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvudiv expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvurem() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvurem a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvurem expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvshl() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvshl a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvshl expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvlshr() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvlshr a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvlshr expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvult() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvult a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvult expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvcomp() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 1))
            |(assert (= c (bvcomp a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<1>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvcomp expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsub() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvsub a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvsub expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsdiv() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvsdiv a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvsdiv expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsrem() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvsrem a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvsrem expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsmod() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvsmod a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvsmod expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvashr() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(declare-const c (_ BitVec 8))
            |(assert (= c (bvashr a b)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |declare-const c BitVec<8>
            |expr_0 = c
            |expr_1 = a
            |expr_2 = b
            |expr_3 = bvashr expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvule() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvule a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvule expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvugt() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvugt a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvugt expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvuge() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvuge a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvuge expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvslt() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvslt a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvslt expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsle() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvsle a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvsle expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsgt() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvsgt a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvsgt expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_bvsge() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (bvsge a b))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = a
            |expr_1 = b
            |expr_2 = bvsge expr_0 expr_1
            |cktrue expr_2
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_extract() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 4))
            |(assert (= b ((_ extract 3 0) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<4>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = extract 0 3 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_repeat() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 4))
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ repeat 2) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<4>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = repeat 2 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_zero_extend() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 4))
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ zero_extend 4) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<4>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = zero_extend 4 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_sign_extend() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 4))
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ sign_extend 4) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<4>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = sign_extend 4 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_rotate_left() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ rotate_left 2) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = rotate_left 2 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_rotate_right() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(declare-const b (_ BitVec 8))
            |(assert (= b ((_ rotate_right 2) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = rotate_right 2 expr_1
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_store() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            |(declare-const c (_ BitVec 8))
            |(declare-const d (Array (_ BitVec 8) (_ BitVec 8)))
            |(assert (= (store d #x01 (bvadd c #x02)) (store a #x01 c)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVecArray<8, 8, 1>
            |declare-const c BitVec<8>
            |declare-const d BitVecArray<8, 8, 1>
            |expr_0 = d
            |expr_1 = bvx8#01
            |expr_2 = c
            |expr_3 = bvx8#02
            |expr_4 = bvadd expr_2 expr_3
            |expr_5 = store expr_0 expr_1 expr_4
            |expr_6 = a
            |expr_7 = bvx8#01
            |expr_8 = c
            |expr_9 = store expr_6 expr_7 expr_8
            |expr_10 = eq expr_5 expr_9
            |cktrue expr_10
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_const_select() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            |(declare-const b (_ BitVec 8))
            |(assert (= b (select a #x01)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const a BitVecArray<8, 8, 1>
            |declare-const b BitVec<8>
            |expr_0 = b
            |expr_1 = a
            |expr_2 = bvx8#01
            |expr_3 = select expr_1 expr_2
            |expr_4 = eq expr_0 expr_3
            |cktrue expr_4
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_const_bvarray() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(assert (= #x01 (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        // The order is undecidable.
        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |expr_0 = bvx8#01
            |expr_1 = bvx8#02
            |expr_2 = constbva 8 8 expr_1
            |expr_3 = a
            |expr_4 = select expr_2 expr_3
            |expr_5 = eq expr_0 expr_4
            |cktrue expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_const_bvarray_on_duplicate_terms() {
        crate::mir::reset_ref_id_count();
        let src = r#"
            |(set-logic ALL)
            |(declare-const a (_ BitVec 8))
            |(assert (= #x01 (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) a)))
        "#
        .trim_margin()
        .unwrap();
        let smt_program = parse_str(&src).unwrap();
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        // The order is undecidable.
        assert_eq!(
            r#"
            |declare-const a BitVec<8>
            |expr_0 = bvx8#01
            |expr_1 = bvx8#01
            |expr_2 = constbva 8 8 expr_1
            |expr_3 = a
            |expr_4 = select expr_2 expr_3
            |expr_5 = eq expr_1 expr_4
            |cktrue expr_5
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }

    #[test]
    fn test_cb() {
        let smt_program = parse_str(
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
        let analyzed = Analyzer::new().analyze(&smt_program).unwrap();
        let fuzz_program = SMT2Fuzz::no_opt().compile(&analyzed).unwrap();
        let tmp = format!("{}", fuzz_program);

        assert_eq!(
            r#"
            |declare-const x BitVec<32>
            |declare-cb abs (int/BitVec<32>) -> int/BitVec<32>
            |expr_0 = bvx32#00000001
            |expr_1 = x
            |expr_2 = (abs expr_1)
            |expr_3 = eq expr_0 expr_2
            |cktrue expr_3
        "#
            .trim_margin()
            .unwrap(),
            tmp.trim()
        );
    }
}
