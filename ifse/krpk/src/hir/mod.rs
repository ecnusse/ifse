//! A high-level IR representing SMT-LIB commands as ASTs. The tokens and AST nodes corresponds to syntax constructs defined in SMT-LIB Standard 2.6
//! one-to-one.

mod ast;
pub mod response;
mod token;

pub use ast::*;
pub use token::*;
