// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};

use crate::dump_str;
use crate::parser::dump::Dump;
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub enum IntLiteral {
    Int(u64),
    UInt(u64),
    Long(u64),
    ULong(u64),
    LongLong(u64),
    ULongLong(u64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Integer {
    pub value: IntLiteral,
}

impl Into<u64> for &IntLiteral {
    fn into(self) -> u64 {
        use IntLiteral::*;
        match *self {
            Int(n) | UInt(n) | Long(n) | ULong(n) | LongLong(n) | ULongLong(n) => n,
        }
    }
}

impl ToString for Integer {
    fn to_string(&self) -> String {
        format!("{}", Into::<u64>::into(&self.value))
    }
}

impl Dump for Integer {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FloatLiteral {
    Float(f64),
    Double(f64),
    LongDouble(f64),
    FloatUD(Box<(f64, String)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Float {
    pub value: FloatLiteral,
}

impl Into<f64> for &FloatLiteral {
    fn into(self) -> f64 {
        use FloatLiteral::*;
        match &*self {
            Float(x) | Double(x) | LongDouble(x) => *x,
            FloatUD(ref x) => x.0,
        }
    }
}

impl ToString for Float {
    fn to_string(&self) -> String {
        match &self.value {
            FloatLiteral::FloatUD(x) => format!("{}{}", x.0, x.1),
            x => format!("{}", Into::<f64>::into(x)),
        }
    }
}

impl Dump for Float {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum CharLiteral {
    Char(u32),
    LChar(u32),
    UChar(u32),
    UUChar(u32),
    U8Char(u32),
    CharUD(Box<(u32, String)>),
    LCharUD(Box<(u32, String)>),
    UCharUD(Box<(u32, String)>),
    UUCharUD(Box<(u32, String)>),
    U8CharUD(Box<(u32, String)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Char {
    pub value: CharLiteral,
}

impl Into<u32> for &CharLiteral {
    fn into(self) -> u32 {
        use CharLiteral::*;
        match &*self {
            Char(x) | LChar(x) | UChar(x) | UUChar(x) | U8Char(x) => *x,
            CharUD(ref x) | LCharUD(ref x) | UCharUD(ref x) | UUCharUD(ref x) | U8CharUD(ref x) => {
                x.0
            }
        }
    }
}

impl ToString for Char {
    fn to_string(&self) -> String {
        use CharLiteral::*;
        match &self.value {
            CharUD(x) | LCharUD(x) | UCharUD(x) | UUCharUD(x) | U8CharUD(x) => {
                if let Some(c) = std::char::from_u32(x.0) {
                    format!("'{}'{}", c, x.1)
                } else {
                    format!("'\\x{:x}'{}", x.0, x.1)
                }
            }
            x => {
                let x = Into::<u32>::into(x);
                if let Some(c) = std::char::from_u32(x) {
                    format!("'{}'", c)
                } else {
                    format!("'\\x{:x}'", x)
                }
            }
        }
    }
}

impl Dump for Char {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum StrLiteral {
    Str(String),
    LStr(String),
    UStr(String),
    UUStr(String),
    U8Str(String),
    RStr(String),
    LRStr(String),
    URStr(String),
    UURStr(String),
    U8RStr(String),
    StrUD(Box<(String, String)>),
    LStrUD(Box<(String, String)>),
    UStrUD(Box<(String, String)>),
    UUStrUD(Box<(String, String)>),
    U8StrUD(Box<(String, String)>),
    RStrUD(Box<(String, String)>),
    LRStrUD(Box<(String, String)>),
    URStrUD(Box<(String, String)>),
    UURStrUD(Box<(String, String)>),
    U8RStrUD(Box<(String, String)>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Str {
    pub value: StrLiteral,
}

impl ToString for Str {
    fn to_string(&self) -> String {
        use StrLiteral::*;
        match &self.value {
            Str(s) | LStr(s) | UStr(s) | UUStr(s) | U8Str(s) | RStr(s) | LRStr(s) | URStr(s)
            | UURStr(s) | U8RStr(s) => format!("\"{}\"", s),

            StrUD(x) | LStrUD(x) | UStrUD(x) | UUStrUD(x) | U8StrUD(x) | RStrUD(x) | LRStrUD(x)
            | URStrUD(x) | UURStrUD(x) | U8RStrUD(x) => format!("\"{}\"{}", x.0, x.1),
        }
    }
}

impl Dump for Str {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bool {
    pub value: bool,
}

impl ToString for Bool {
    fn to_string(&self) -> String {
        if self.value {
            "true".to_string()
        } else {
            "false".to_string()
        }
    }
}

impl Dump for Bool {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

pub(crate) struct StringLiteralParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> StringLiteralParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    #[inline(always)]
    fn concat(first: &str, lens: usize, strings: Vec<String>) -> String {
        let mut res = String::with_capacity(lens + first.len() + 1);
        res.push_str(first);
        for s in strings {
            res.push_str(&s);
        }
        res
    }

    pub(crate) fn parse(self, first: &str) -> (Option<Token>, String) {
        let mut strings = Vec::with_capacity(32); // TODO: put a good value here if it's useful
        let mut lens = 0;

        let tok = loop {
            let tok = self.lexer.next_useful();
            match tok {
                Token::LiteralString(s)
                | Token::LiteralLString(s)
                | Token::LiteralUString(s)
                | Token::LiteralUUString(s)
                | Token::LiteralU8String(s)
                | Token::LiteralRString(s)
                | Token::LiteralLRString(s)
                | Token::LiteralURString(s)
                | Token::LiteralUURString(s)
                | Token::LiteralU8RString(s) => {
                    lens += s.len();
                    strings.push(s);
                }
                Token::LiteralStringUD(s_suf)
                | Token::LiteralLStringUD(s_suf)
                | Token::LiteralUStringUD(s_suf)
                | Token::LiteralUUStringUD(s_suf)
                | Token::LiteralU8StringUD(s_suf)
                | Token::LiteralRStringUD(s_suf)
                | Token::LiteralLRStringUD(s_suf)
                | Token::LiteralURStringUD(s_suf)
                | Token::LiteralUURStringUD(s_suf)
                | Token::LiteralU8RStringUD(s_suf) => {
                    lens += s_suf.0.len();
                    strings.push(s_suf.0);
                }
                _ => {
                    break tok;
                }
            }
        };

        (Some(tok), Self::concat(first, lens, strings))
    }
}
