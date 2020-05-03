// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

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

#[derive(Clone, Debug, PartialEq)]
pub struct Bool {
    pub value: bool,
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

    pub(crate) fn parse(self, first: &str) -> (Option<LocToken>, String) {
        let mut strings = Vec::with_capacity(32); // TODO: put a good value here if it's useful
        let mut lens = 0;

        let tok = loop {
            let tok = self.lexer.next_useful();
            match tok.tok {
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
