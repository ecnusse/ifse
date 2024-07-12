#[macro_use]
extern crate match_template;

use std::ffi::CString;
use std::fmt;

pub mod fuzzend;
mod fuzzsolver;
pub mod hir;
mod location;
pub mod mir;
pub mod smt2fuzz;
pub mod smtanalyze;
pub mod smtparser;

use fuzzend::Solution;
pub use fuzzsolver::*;
pub use hir::response;
use hir::Attribute;
use hir::Hexadecimal;
pub use hir::Numeral;
use hir::SMTScript;
pub use hir::Sort;
use hir::SpecConstant;

pub use location::{HasPosition, Located, Position, Span};

/// Printable list.
pub(crate) struct PrintableList<'a, T: 'a>(&'a Vec<T>);

impl<'a, T: 'a + fmt::Display> fmt::Display for PrintableList<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.split_first() {
            Some((e, list)) => {
                e.fmt(f)?;
                for e in list.iter() {
                    write!(f, " ")?;
                    e.fmt(f)?
                }
            }
            None => (),
        }

        Ok(())
    }
}

impl<'a, T: 'a + fmt::Debug> fmt::Debug for PrintableList<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.split_first() {
            Some((e, list)) => {
                e.fmt(f)?;
                for e in list.iter() {
                    write!(f, " ")?;
                    e.fmt(f)?
                }
            }
            None => (),
        }

        Ok(())
    }
}

// C APIs
include!("api.rs");
