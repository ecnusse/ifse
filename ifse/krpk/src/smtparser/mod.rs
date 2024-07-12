//! `smtparser` takes input conforming to SMT-LIB Standard 2.6 and produces a hir AST. It consists of a lexer and a parser, both written using
//! parser combinators from the `combine` crate. They generally follows the grammar on page 45 of the standard and are in a CFG form.

mod lexer;
mod parser;

use combine::easy::Errors;
use combine::stream::PointerOffset;
pub use lexer::*;
pub use parser::*;

use crate::hir::Token;

#[derive(Debug)]
pub enum SMTParserError<'a> {
    LexError(Errors<char, &'a str, PointerOffset<str>>),
    ParseError(Errors<Token, Vec<Token>, PointerOffset<[Token]>>),
}
