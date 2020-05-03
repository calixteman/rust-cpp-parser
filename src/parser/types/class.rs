// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use bitflags::bitflags;

bitflags! {
    pub struct Specifier: u8 {
        pub const PRIVATE = 0;
        pub const PUBLIC = 0b1;
        pub const PROTECTED = 0b10;
        pub const VIRTUAL = 0b100;
    }
}

impl Specifier {
    pub(crate) fn from_tok(&mut self, tok: Token) {
        match tok {
            Token::Private => {
                self.set(Specifier::PRIVATE);
            }
            Token::Public => {
                self.set(Specifier::PUBLIC);
            }
            Token::Protected => {
                self.set(Specifier::PROTECTED);
            }
            Token::Virtual => {
                self.set(Specifier::VIRTUAL);
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
    pub enum Key {
    Class,
    Struct,
}

#[derive(Clone, Debug, PartialEq)]
    pub struct Class {
    pub key: Key,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub final: bool,
    pub base: Vec<Derived>,
    pub members: Option<()>,
}

#[derive(Clone, Debug, PartialEq)]
    pub struct Derived {
    pub base: Class,
    pub specifier: Specifier,
}

mod attribute {
    pub struct Simple {
        pub name: String,
    }

    pub struct Args {
        pub id: String,
    }

    pub struct Attribute {

    }
}

