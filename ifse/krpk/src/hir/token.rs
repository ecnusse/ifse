//! This module defines lexical tokens that generally conforms to the syntax described by SMT-LIB Standard 2.6.

use std::fmt;

use std::iter::repeat;

use itertools::Itertools;

use crate::{Located, Span};

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Hexadecimal {
    pub digit_num: usize,
    pub bytes: Vec<u8>,
}

impl Hexadecimal {
    pub fn to_string(&self) -> String {
        let mut tmp = Vec::with_capacity(self.bytes.len());
        for byte in self.bytes.iter() {
            tmp.push(format!("{:02x}", byte));
        }
        tmp.reverse();
        let mut r = tmp.join("");
        if self.digit_num % 2 == 0 {
            r
        } else {
            r.remove(0);
            r
        }
    }

    pub fn bit_num(&self) -> usize {
        self.digit_num * 4
    }

    pub fn parse(text: &str) -> Result<Hexadecimal, ()> {
        let owned = text.to_owned();
        let (text_, digit_num) = if text.starts_with("#x") {
            let dn = owned.len() - 2;
            (
                if text.len() % 2 == 0 {
                    owned[2..].to_owned()
                } else {
                    format!("0{}", &owned[2..])
                },
                dn,
            )
        } else {
            let dn = owned.len();
            (
                if text.len() % 2 == 0 {
                    owned
                } else {
                    format!("0{}", owned)
                },
                dn,
            )
        };
        let mut bytes = Vec::with_capacity(text_.len() / 2);
        for i in (0..text_.len()).step_by(2) {
            let byte = u8::from_str_radix(&text_[i..i + 2], 16).map_err(|_| ())?;
            bytes.push(byte);
        }
        Ok(Hexadecimal {
            digit_num,
            bytes: bytes.into_iter().rev().collect_vec(),
        })
    }

    pub fn concat(&self, another: &Hexadecimal) -> Hexadecimal {
        assert!(another.bit_num() % 8 == 0 || another.bit_num() % 8 == 4);
        let aligned = another.bit_num() % 8 == 0;
        let mut bytes = self.bytes.clone();
        let mut another_bytes = another.bytes.clone();
        if aligned {
            another_bytes.append(&mut bytes);
        } else {
            let mut tmp = another_bytes.clone();
            for b in bytes {
                let first_half = b & 0xf;
                let second_half = b & 0xf0 >> 4;
                tmp.last_mut().map(|b| *b |= first_half << 4);
                tmp.push(second_half);
            }
        }
        Hexadecimal {
            digit_num: self.digit_num + another.digit_num,
            bytes: another_bytes,
        }
    }

    pub fn value(&self) -> Option<u64> {
        if self.bit_num() > 64 {
            return None;
        }
        let mut value = 0u64;
        for byte in self.bytes.iter().rev() {
            value <<= 8;
            value |= *byte as u64;
        }
        Some(value)
    }
}

impl fmt::Display for Hexadecimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#x{}", self.to_string())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Binary {
    pub digit_num: usize,
    pub bytes: Vec<u8>,
}

impl Binary {
    pub fn to_string(&self) -> String {
        let mut tmp = Vec::with_capacity(self.bytes.len());
        for byte in self.bytes.iter().rev() {
            tmp.push(format!("{:08b}", byte));
        }
        tmp.reverse();
        let mut r = tmp.join("");
        for _ in 0..(8 - self.digit_num % 8) {
            r.remove(0);
        }
        r
    }

    pub fn bit_num(&self) -> usize {
        self.digit_num
    }

    pub fn parse(text: &str) -> Result<Self, ()> {
        let owned = text.to_owned();
        let (text_, digit_num) = if text.starts_with("#b") {
            let dn = owned.len() - 2;
            let padding_num = (8 - dn % 8) % 8;
            let tmp = format!(
                "{}{}",
                repeat("0").take(padding_num).collect::<String>(),
                owned[2..].to_owned(),
            );
            (tmp, dn)
        } else {
            let dn = owned.len();
            let padding_num = (8 - dn % 8) % 8;
            let tmp = format!(
                "{}{}",
                repeat("0").take(padding_num).collect::<String>(),
                owned,
            );
            (tmp, dn)
        };
        let mut bytes = Vec::with_capacity(text_.len() / 8);
        for i in (0..text_.len()).step_by(8) {
            let byte = u8::from_str_radix(&text_[i..i + 8], 2).map_err(|_| ())?;
            bytes.push(byte);
        }
        Ok(Binary { digit_num, bytes })
    }

    pub fn concat(&self, another: &Binary) -> Binary {
        let residual = 8 - another.bit_num() % 8;
        let mut bytes = self.bytes.clone();
        let mut another_bytes = another.bytes.clone();
        if residual == 0 {
            another_bytes.append(&mut bytes);
        } else {
            let mut tmp = another_bytes.clone();
            for b in bytes {
                let first_half = b << (8 - residual);
                let second_half = b >> residual;
                tmp.last_mut().map(|b| *b |= first_half);
                tmp.push(second_half);
            }
        }
        Binary {
            digit_num: self.digit_num + another.digit_num,
            bytes: another_bytes,
        }
    }

    pub fn value(&self) -> Option<u64> {
        if self.bit_num() > 64 {
            return None;
        }
        let mut value = 0u64;
        for byte in self.bytes.iter().rev() {
            value <<= 8;
            value |= *byte as u64;
        }
        Some(value)
    }
}

impl From<Hexadecimal> for Binary {
    fn from(hex: Hexadecimal) -> Binary {
        Binary {
            digit_num: hex.digit_num * 4,
            bytes: hex.bytes,
        }
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#b{}", self.to_string())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Reserved {
    Underscore,
    Exclamation,
    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,
}

impl fmt::Display for Reserved {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Reserved::*;
        match self {
            Underscore => write!(f, "_"),
            Exclamation => write!(f, "!"),
            As => write!(f, "as"),
            Let => write!(f, "let"),
            Exists => write!(f, "exists"),
            Forall => write!(f, "forall"),
            Match => write!(f, "match"),
            Par => write!(f, "par"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Symbol {
    Simple(String),
    Quoted(String),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Symbol::*;
        match self {
            Simple(s) => write!(f, "{}", s),
            Quoted(s) => write!(f, "|{}|", s),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Keyword(pub String);

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, ":{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Numeral(pub usize);

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Decimal {
    pub integer_part: Vec<u8>,
    pub decimal_part: Vec<u8>,
}

impl Decimal {
    pub fn to_string(&self) -> String {
        let mut tmp = Vec::with_capacity(self.integer_part.len());
        for byte in self.integer_part.iter().rev() {
            assert!(*byte < 10u8);
            tmp.push(format!("{}", byte));
        }
        tmp.reverse();
        let mut r = tmp.join("");
        if self.integer_part.len() == 0 {
            r.push('0');
        }
        if self.decimal_part.len() > 0 {
            r.push('.');
            for byte in self.decimal_part.iter() {
                assert!(*byte < 10u8);
                r.push_str(&format!("{}", byte));
            }
        }
        r
    }

    pub fn parse(text: &str) -> Result<Self, ()> {
        let mut integer_part = Vec::new();
        let mut decimal_part = Vec::new();
        let mut decimal_part_flag = false;
        for c in text.chars() {
            if c == '.' {
                decimal_part_flag = true;
                continue;
            }
            let byte = c.to_digit(10).ok_or(())? as u8;
            if decimal_part_flag {
                decimal_part.push(byte);
            } else {
                integer_part.push(byte);
            }
        }
        if !decimal_part_flag {
            return Err(());
        }
        Ok(Decimal {
            integer_part,
            decimal_part,
        })
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Display for Numeral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Numeral {
    pub fn parse(text: &str) -> Result<Numeral, ()> {
        let num = text.parse::<usize>().map_err(|_| ())?;
        Ok(Numeral(num))
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct StringLiteral(pub String);

impl fmt::Display for StringLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

// TODO: Support Decimals.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Token {
    LParen,
    RParen,

    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    StringLiteral(StringLiteral),
    Reserved(Reserved),
    Symbol(Symbol),
    Keyword(Keyword),
}

impl Token {
    pub fn at(self, span: Span) -> Located<Token> {
        Located::new(self, span)
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::*;
        match self {
            Numeral(num) => write!(f, "{}", num),
            Hexadecimal(hex) => write!(f, "{}", hex),
            Binary(bin) => write!(f, "{}", bin),
            StringLiteral(string) => write!(f, "\"{}\"", string),
            Reserved(reserved) => write!(f, "{}", reserved),
            Symbol(symbol) => write!(f, "{}", symbol),
            Keyword(keyword) => write!(f, "{}", keyword),
            LParen => write!(f, "("),
            RParen => write!(f, ")"),
            Decimal(decimal) => write!(f, "{}", decimal),
        }
    }
}
