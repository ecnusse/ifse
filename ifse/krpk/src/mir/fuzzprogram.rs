use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

use std::rc::Rc;

use crate::smtanalyze::KRPKIdentifier;

use super::{DeclaredCBFunction, DeclaredConstant, IRRef, MutableIRRef, Type};
use combine::parser::combinator::Either;
use itertools::Itertools;
use sorted_vec::SortedVec;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct MemoryProxy {
    pub size: u64,
    pub min_addr: u64,
}

impl MemoryProxy {
    pub fn name(&self) -> String {
        format!("mem_proxy_{}_{}", self.min_addr, self.size)
    }
}

impl fmt::Display for MemoryProxy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}<{}, {}>", self.name(), self.min_addr, self.size)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuzzProgram {
    unknowns: HashMap<KRPKIdentifier, Rc<DeclaredConstant>>,
    cb_functions: HashMap<KRPKIdentifier, Rc<DeclaredCBFunction>>,

    ctype_smt_correspondence: HashMap<String, Type>,
    memory_proxy: Option<MemoryProxy>,

    entry_points: HashSet<MutableIRRef>,
}

impl fmt::Display for FuzzProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(memory) = &self.memory_proxy {
            writeln!(f, "memory-proxy {}", memory)?;
        }
        for unknown in self
            .unknowns
            .values()
            .sorted_by(|e1, e2| e1.name.cmp(&e2.name))
        {
            writeln!(f, "declare-const {} {}", unknown.name, unknown.type_)?;
        }
        for cb_function in self.cb_functions.values() {
            write!(f, "declare-cb {} (", cb_function.id,)?;
            let mut first = true;
            for (smt_type, c_type) in cb_function.params.iter() {
                if !first {
                    write!(f, " ")?;
                } else {
                    first = false;
                }
                write!(f, "{}/{}", c_type, smt_type)?;
            }
            write!(
                f,
                ") -> {}/{}\n",
                cb_function.return_smt_and_c_type.1, cb_function.return_smt_and_c_type.0
            )?;
        }
        let mut errors = Vec::new();
        self.visit(|ir_ref| {
            let tmp = writeln!(f, "{}", ir_ref.borrow());
            if let Err(err) = tmp {
                errors.push(err);
            };
        });
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.into_iter().next().unwrap())
        }
    }
}

struct MaySortedVec<T: Ord>(Either<Vec<T>, SortedVec<T>>);

impl<T: Ord> MaySortedVec<T> {
    fn from_unsorted(vec: Vec<T>) -> Self {
        #[cfg(test)]
        {
            return Self(Either::Right(SortedVec::from_unsorted(vec)));
        }
        Self(Either::Left(vec))
    }

    fn push(&mut self, value: T) {
        match &mut self.0 {
            Either::Left(vec) => vec.push(value),
            Either::Right(sorted_vec) => {
                sorted_vec.push(value);
            }
        };
    }

    fn pop(&mut self) -> Option<T> {
        match &mut self.0 {
            Either::Left(vec) => vec.pop(),
            Either::Right(sorted_vec) => sorted_vec.pop(),
        }
    }
}

impl FuzzProgram {
    pub(crate) fn new(
        unknowns: HashMap<KRPKIdentifier, Rc<DeclaredConstant>>,
        mem_info: Option<(u64, u64)>,
        cb_functions: HashMap<KRPKIdentifier, Rc<DeclaredCBFunction>>,
        ctype_smt_correspondence: HashMap<String, Type>,
        entry_points: HashSet<MutableIRRef>,
    ) -> Self {
        Self {
            unknowns,
            cb_functions,
            ctype_smt_correspondence,
            entry_points,
            memory_proxy: mem_info.map(|(min_addr, size)| MemoryProxy { size, min_addr }),
        }
    }

    pub(crate) fn memory_proxy(&self) -> Option<MemoryProxy> {
        self.memory_proxy.clone()
    }

    pub fn remove_entries_that(&mut self, predicate: impl Fn(&IRRef) -> bool) {
        let mut to_remove = vec![];
        for entry in &self.entry_points {
            if predicate(&entry.clone().into()) {
                to_remove.push(entry.clone());
            }
        }

        let mut removed = HashSet::new();
        let mut collect_removed = |entry: &MutableIRRef| {
            let mut work_list: VecDeque<IRRef> = VecDeque::new();
            work_list.push_back(entry.clone().into());
            while let Some(h) = work_list.pop_front() {
                if !removed.insert(h.clone()) {
                    continue;
                }
                for succ in h.borrow().successors() {
                    work_list.push_back(succ.clone());
                }
            }
        };

        for entry in &to_remove {
            self.entry_points.remove(entry);
            collect_removed(entry);
        }

        self.visit_mut(|ir| {
            ir.remove_refed_that(|t| removed.contains(&t.clone().into()));
        })
    }

    pub fn add_entry(&mut self, entry: MutableIRRef) {
        self.entry_points.insert(entry);
    }

    pub fn add_entires(&mut self, entries: impl IntoIterator<Item = MutableIRRef>) {
        self.entry_points.extend(entries);
    }

    pub fn lookup_ctype(&self, type_: &Type) -> Option<String> {
        self.ctype_smt_correspondence
            .iter()
            .find(|(_, v)| *v == type_)
            .map(|(e, _)| e.clone())
    }

    pub fn lookup_smt_type(&self, ctype: &str) -> Option<Type> {
        self.ctype_smt_correspondence.get(ctype).map(|e| e.clone())
    }

    pub fn lookup_unknown(&self, id: &KRPKIdentifier) -> Option<Rc<DeclaredConstant>> {
        self.unknowns.get(id).map(|e| e.clone())
    }

    // pub fn stmts(&self) -> Vec<Rc<Stmt>> {
    //     self.stmts.borrow().clone()
    // }

    pub fn lookup_cb_function(&self, id: &KRPKIdentifier) -> Option<Rc<DeclaredCBFunction>> {
        self.cb_functions.get(id).map(|e| e.clone())
    }

    pub fn unknowns(&self) -> impl Iterator<Item = Rc<DeclaredConstant>> + '_ {
        self.unknowns.values().map(|e| e.clone())
    }

    pub fn cb_functions(&self) -> impl Iterator<Item = Rc<DeclaredCBFunction>> + '_ {
        self.cb_functions.values().map(|e| e.clone())
    }

    /// Visit each SSA instruction in the topological order and modify them.
    pub fn visit_mut(&mut self, mut visitor: impl FnMut(MutableIRRef)) {
        #[derive(Debug, Hash, Clone)]
        struct Pair(usize, IRRef);
        impl PartialOrd for Pair {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                match self.0.cmp(&other.0) {
                    std::cmp::Ordering::Equal => self.1.partial_cmp(&other.1),
                    other => Some(other),
                }
            }
        }
        impl Ord for Pair {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                match self.0.cmp(&other.0) {
                    std::cmp::Ordering::Equal => self.1.cmp(&other.1),
                    other => other,
                }
            }
        }
        impl PartialEq for Pair {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0 && self.1 == other.1
            }
        }
        impl Eq for Pair {}

        let mut queue =
            MaySortedVec::from_unsorted(self.entry_points.iter().cloned().collect_vec());
        let mut to_visit = BTreeSet::<Pair>::new();
        let mut to_visit_map = HashMap::<IRRef, usize>::new();
        while let Some(current) = queue.pop() {
            visitor(current.clone());
            let mut to_decrement = Vec::new();
            for succ in current.borrow().successors() {
                to_decrement.push(succ.clone());
            }
            for to_decrement in to_decrement {
                if let Some(old_count) = to_visit_map.get(&to_decrement).cloned() {
                    to_visit.remove(&Pair(old_count, to_decrement.clone()));
                    to_visit_map.insert(to_decrement.clone(), old_count - 1);
                    to_visit.insert(Pair(old_count - 1, to_decrement.clone()));
                } else {
                    to_visit_map.insert(
                        to_decrement.clone(),
                        to_decrement.borrow().predecessor_num() - 1,
                    );
                    to_visit.insert(Pair(
                        to_decrement.borrow().predecessor_num() - 1,
                        to_decrement.clone(),
                    ));
                }
            }
            let mut to_derecord = Vec::new();
            for pair @ Pair(count, to_add) in &to_visit {
                if *count != 0 {
                    break;
                }

                queue.push(to_add.clone().into());
                to_derecord.push(pair.clone());
            }

            for to_derecord in to_derecord {
                let tmp = to_visit.remove(&to_derecord);
                assert!(tmp);
                let tmp = to_visit_map.remove(&to_derecord.1);
                assert!(tmp.is_some());
            }
        }
    }

    /// Visit each SSA instruction in the topological order without modifying them.
    pub fn visit(&self, mut visitor: impl FnMut(IRRef)) {
        #[derive(Debug, Hash, Clone)]
        struct Pair(usize, IRRef);
        impl PartialOrd for Pair {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                match self.0.cmp(&other.0) {
                    std::cmp::Ordering::Equal => self.1.partial_cmp(&other.1),
                    other => Some(other),
                }
            }
        }
        impl Ord for Pair {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                match self.0.cmp(&other.0) {
                    std::cmp::Ordering::Equal => self.1.cmp(&other.1),
                    other => other,
                }
            }
        }
        impl PartialEq for Pair {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0 && self.1 == other.1
            }
        }

        impl Eq for Pair {}

        let mut queue =
            MaySortedVec::from_unsorted(self.entry_points.iter().cloned().collect_vec());
        let mut to_visit = BTreeSet::<Pair>::new();
        let mut to_visit_map = HashMap::<IRRef, usize>::new();
        while let Some(current) = queue.pop() {
            visitor(current.clone().into());
            let mut to_decrement = Vec::new();
            for succ in current.borrow().successors() {
                to_decrement.push(succ.clone());
            }
            for to_decrement in to_decrement {
                if let Some(old_count) = to_visit_map.get(&to_decrement).cloned() {
                    to_visit.remove(&Pair(old_count, to_decrement.clone()));
                    to_visit_map.insert(to_decrement.clone(), old_count - 1);
                    to_visit.insert(Pair(old_count - 1, to_decrement.clone()));
                } else {
                    to_visit_map.insert(
                        to_decrement.clone(),
                        to_decrement.borrow().predecessor_num() - 1,
                    );
                    to_visit.insert(Pair(
                        to_decrement.borrow().predecessor_num() - 1,
                        to_decrement.clone(),
                    ));
                }
            }

            let mut to_derecord = Vec::new();
            for pair @ Pair(count, to_add) in &to_visit {
                if *count != 0 {
                    break;
                }

                to_derecord.push(pair.clone());
                queue.push(to_add.clone().into());
            }

            for to_derecord in to_derecord {
                let tmp = to_visit.remove(&to_derecord);
                assert!(tmp);
                let tmp = to_visit_map.remove(&to_derecord.1);
                assert!(tmp.is_some());
            }
        }
    }
}
