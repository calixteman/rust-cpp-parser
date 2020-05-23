// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use termcolor::StandardStreamLock;

use crate::lexer::Token;
use crate::parser::dump::Dump;

bitflags! {
    pub struct CVQualifier: u8 {
        const CONST = 0b1;
        const VOLATILE = 0b10;
        const RESTRICT = 0b100;
    }
}

impl ToString for CVQualifier {
    fn to_string(&self) -> String {
        bitflags_to_str!(self, Self, CONST, "const", VOLATILE, "volatile", RESTRICT, "restrict")
    }
}

impl Dump for CVQualifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

impl CVQualifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Const => {
                *self |= Self::CONST;
                true
            }
            Token::Volatile => {
                *self |= Self::VOLATILE;
                true
            }
            Token::Restrict => {
                *self |= Self::RESTRICT;
                true
            }
            _ => false,
        }
    }

    pub(crate) fn is_cv(tok: &Token) -> bool {
        match tok {
            Token::Const | Token::Volatile | Token::Restrict => true,
            _ => false,
        }
    }
}
