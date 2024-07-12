use core::fmt;
use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;

use crate::mir::{DeclaredConstant, LiteralValue};

/// The response returned by a fuzzer.
#[derive(Debug, Clone)]
pub struct Model {
    mapping: HashMap<Rc<DeclaredConstant>, LiteralValue>,
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (constant, value) in self.mapping.iter().sorted() {
            writeln!(f, "{} := {}", constant.name, value)?;
        }
        Ok(())
    }
}

impl Model {
    pub(super) fn new() -> Self {
        Self {
            mapping: HashMap::new(),
        }
    }

    pub(super) fn with_values(values: HashMap<Rc<DeclaredConstant>, LiteralValue>) -> Self {
        Self { mapping: values }
    }

    pub fn value_of(&self, constant: &DeclaredConstant) -> Option<&LiteralValue> {
        self.mapping.get(constant)
    }

    // pub fn ext_value_of(&self, constant: &DeclaredConstant) -> &LiteralValue {
    //     self.mapping.get(constant).unwrap_or(match &constant.type_ {
    //         crate::mir::Type::BitVec(w) => {
    //             &LiteralValue::BitVecValue(w, vec![0; (w + 7) / 8])
    //         }
    //         crate::mir::Type::Bool => &LiteralValue::BoolValue(false),
    //         crate::mir::Type::BitVecArray { upper_bound, .. } => {
    //             let Some(upper_bound) = upper_bound else {unreachable!()};
    //             &LiteralValue::BitVecArrayValue(upper_bound, vec![0; upper_bound])
    //         }
    //     })
    // }

    // pub fn ext_value_by_name(&self, name: &str) -> &LiteralValue {
    //     self.mapping
    //         .iter()
    //         .find(|(constant, _)| constant.name == name)
    //         .map(|(_, value)| value)
    //         .unwrap_or(
    //             match  {

    //             }
    //         )
    // }

    pub fn value_by_name(&self, name: &str) -> Option<&LiteralValue> {
        self.mapping
            .iter()
            .find(|(constant, _)| constant.name == name)
            .map(|(_, value)| value)
    }

    pub fn contains_unknown(&self, unknown: &DeclaredConstant) -> bool {
        self.mapping.contains_key(unknown)
    }

    pub fn contains_unknown_by_name(&self, name: &str) -> bool {
        self.mapping
            .iter()
            .any(|(constant, _)| constant.name == name)
    }

    pub fn size(&self) -> usize {
        self.mapping.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Rc<DeclaredConstant>, &LiteralValue)> {
        self.mapping.iter()
    }
}
