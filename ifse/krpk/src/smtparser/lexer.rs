use crate::hir::{
    Binary, Decimal, Hexadecimal, Keyword, Numeral, Reserved, StringLiteral, Symbol, Token,
};

use combine::easy::{Errors, Stream as EasyStream};
use combine::parser::char::{char, spaces, string};
use combine::parser::function::parser as fparser;
use combine::parser::regex::{captures, find};
use combine::parser::token::token;
use combine::stream::{PointerOffset, StreamOnce};
use combine::{attempt, choice, eof, look_ahead, many, position, satisfy, EasyParser, Parser};
use regex::Regex;

use super::SMTParserError;

impl<'a> From<Errors<char, &'a str, PointerOffset<str>>> for SMTParserError<'a> {
    fn from(value: Errors<char, &'a str, PointerOffset<str>>) -> Self {
        SMTParserError::LexError(value)
    }
}

pub fn lex(text: &str) -> Result<Vec<Token>, Errors<char, &str, PointerOffset<str>>> {
    let lparen = token('(').map(|_| Token::LParen);
    let rparen = token(')').map(|_| Token::RParen);
    let decimal = find(Regex::new(r"^[0-9]+\.[0-9]+").unwrap())
        .map(|dec| Token::Decimal(Decimal::parse(dec).unwrap()));
    let numeral = find(Regex::new(r"^(0|[1-9][0-9]*)").unwrap())
        .map(|num| Token::Numeral(Numeral::parse(num).unwrap()));
    let hexadecimal = find(Regex::new(r"^#x[0-9a-zA-Z]+").unwrap())
        .map(|hex| Token::Hexadecimal(Hexadecimal::parse(hex).unwrap()));
    let binary = find(Regex::new(r"^#b[01]+").unwrap())
        .map(|bin| Token::Binary(Binary::parse(bin).unwrap()));
    let string_literal = fparser(|input: &mut EasyStream<&str>| {
        let single_quote = || char('"').map(|_| (true, '"'));
        let not_quote = || satisfy(|c| c != '"').map(|c| (false, c));
        single_quote().parse_stream(input).into_result()?;
        let mut result = "".to_string();
        loop {
            let mut choice = choice((not_quote(), single_quote()));
            let ((is_single_quote, c), current_commited) =
                choice.parse_stream(input).into_result()?;
            if !is_single_quote {
                result.push(c);
            } else {
                let mut peek = look_ahead(single_quote());
                let peeked = peek.parse_stream(input).into_result();
                if peeked.is_ok() {
                    result.push(c);
                    input.uncons().unwrap();
                } else {
                    return Ok((result, current_commited));
                }
            }
        }
    })
    .map(|string| Token::StringLiteral(StringLiteral(string)));

    let reserved = fparser(|input: &mut EasyStream<&str>| {
        let reserved0 = || {
            choice((
                token('_').map(|_| Token::Reserved(Reserved::Underscore)),
                token('!').map(|_| Token::Reserved(Reserved::Exclamation)),
            ))
        };
        let reserved1 = || {
            choice((
                string("as").map(|_| Token::Reserved(Reserved::As)),
                string("let").map(|_| Token::Reserved(Reserved::Let)),
                string("forall").map(|_| Token::Reserved(Reserved::Forall)),
                string("exists").map(|_| Token::Reserved(Reserved::Exists)),
                string("match").map(|_| Token::Reserved(Reserved::Match)),
                string("par").map(|_| Token::Reserved(Reserved::Par)),
            ))
        };

        if let ok @ Ok(_) = reserved0().parse_stream(input).into_result() {
            return ok;
        }

        let mut lookahead = look_ahead((
            reserved1(),
            find(Regex::new(r"^([^a-zA-Z0-9~!@$%^&*_\-+=<>.?/]|$)").unwrap()),
        ));
        lookahead.parse_stream(input).into_result()?;
        reserved1().parse_stream(input).into_result()
    });

    let symbol = choice((
        find(Regex::new(r"^[a-zA-Z0-9~!@$%^&*_\-+=<>.?/]+").unwrap())
            .map(|name: &str| Token::Symbol(Symbol::Simple(name.to_string()))),
        captures(Regex::new(r#"^\|([^|\\]*)\|"#).unwrap())
            .map(|caps: Vec<&str>| Token::Symbol(Symbol::Quoted(caps[1].to_string()))),
    ));

    let keyword = captures(Regex::new(r"^:([a-zA-Z0-9~!@$%^&*_\-+=<>.?/]+)").unwrap())
        .map(|caps: Vec<&str>| Token::Keyword(Keyword(caps[1].to_string())));

    let token = choice((
        decimal,
        numeral,
        attempt(reserved).or(symbol),
        keyword,
        lparen,
        rparen,
        string_literal,
        hexadecimal,
        binary,
    ));
    let located_token = (position(), token, position()).map(|tuple| {
        let token = tuple.1;
        token
    });
    let skip_spaces = || spaces().silent();
    let mut located_token_sequence = skip_spaces()
        .with(many(located_token.skip(skip_spaces())))
        .skip(skip_spaces())
        .skip(eof());
    let parsed = located_token_sequence.easy_parse(text)?;
    assert!(parsed.1.is_empty());
    Ok(parsed.0)
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_paren() {
        let lp = "(";
        let parsed = lex(lp).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::LParen, parsed[0]);

        let rp = ")";
        let parsed = lex(rp).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::RParen, parsed[0]);
    }

    #[test]
    fn test_num() {
        let num = "123";
        let parsed = lex(num).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Numeral(Numeral(123)), parsed[0]);

        let decimal = "123.0";
        let parsed = lex(decimal).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Decimal(Decimal::parse(decimal).unwrap()), parsed[0]);

        let hex = "#x123";
        let parsed = lex(hex).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(
            Token::Hexadecimal(Hexadecimal::parse(hex).unwrap()),
            parsed[0]
        );

        let bin = "#b101";
        let parsed = lex(bin).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Binary(Binary::parse(bin).unwrap()), parsed[0]);
    }

    #[test]
    fn test_reserved() {
        let underscore = "_";
        let parsed = lex(underscore).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Underscore), parsed[0]);

        let exclamation = "!";
        let parsed = lex(exclamation).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Exclamation), parsed[0]);

        let as_ = "as";
        let parsed = lex(as_).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::As), parsed[0]);

        let let_ = "let";
        let parsed = lex(let_).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Let), parsed[0]);

        let forall = "forall";
        let parsed = lex(forall).unwrap();
        assert_eq!(1, parsed.len());

        let exists = "exists";
        let parsed = lex(exists).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Exists), parsed[0]);

        let match_ = "match";
        let parsed = lex(match_).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Match), parsed[0]);

        let par = "par";
        let parsed = lex(par).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Reserved(Reserved::Par), parsed[0]);
    }

    #[test]
    fn test_symbol() {
        let simple = "abc!_";
        let parsed = lex(simple).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Symbol(Symbol::Simple(simple.to_string())), parsed[0]);

        let quoted = "|!_abc aa|";
        let parsed = lex(quoted).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(
            Token::Symbol(Symbol::Quoted("!_abc aa".to_string())),
            parsed[0]
        );
    }

    #[test]
    fn test_keyword() {
        let keyword = ":abc!_";
        let parsed = lex(keyword).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(Token::Keyword(Keyword("abc!_".to_string())), parsed[0]);
    }

    #[test]
    fn test_string_literal() {
        let text = "\"ab\"\"c\"";
        let parsed = lex(text).unwrap();
        assert_eq!(1, parsed.len());
        assert_eq!(
            Token::StringLiteral(StringLiteral("ab\"c".to_string())),
            parsed[0]
        );
    }

    #[test]
    fn test_complex() {
        let text = r#"(par let def-fun #x11 #b101 "ab""c" 11 11.1)"#;
        let parsed = lex(text).unwrap();
        assert_eq!(10, parsed.len());
        assert_eq!(Token::LParen, parsed[0]);
        assert_eq!(Token::Reserved(Reserved::Par), parsed[1]);
        assert_eq!(Token::Reserved(Reserved::Let), parsed[2]);
        assert_eq!(
            Token::Symbol(Symbol::Simple("def-fun".to_string())),
            parsed[3]
        );
        assert_eq!(
            Token::Hexadecimal(Hexadecimal::parse("#x11").unwrap()),
            parsed[4]
        );
        assert_eq!(Token::Binary(Binary::parse("#b101").unwrap()), parsed[5]);
        assert_eq!(
            Token::StringLiteral(StringLiteral("ab\"c".to_string())),
            parsed[6]
        );
        assert_eq!(Token::Numeral(Numeral(11)), parsed[7]);
        assert_eq!(Token::Decimal(Decimal::parse("11.1").unwrap()), parsed[8]);
        assert_eq!(Token::RParen, parsed[9]);
    }
}
