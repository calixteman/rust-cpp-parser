// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::Token;
use bitflags::bitflags;

use crate::parser::dump::Dump;
use crate::{bitflags_to_str, dump_str};
use termcolor::StandardStreamLock;

bitflags! {
    pub struct Specifier: u32 {
        const TYPEDEF = 0b1;
        const INLINE = 0b10;
        const VIRTUAL = 0b100;
        const EXPLICIT = 0b1000;
        const FRIEND = 0b1_0000;
        const CONSTEVAL = 0b10_0000;
        const CONSTEXPR = 0b100_0000;
        const CONSTINIT = 0b1000_0000;
        const REGISTER = 0b1_0000_0000;
        const STATIC = 0b10_0000_0000;
        const THREAD_LOCAL = 0b100_0000_0000;
        const EXTERN = 0b1000_0000_0000;
        const MUTABLE = 0b1_0000_0000_0000;
        const CDECL = 0b10_0000_0000_0000;
        const CLRCALL = 0b100_0000_0000_0000;
        const FASTCALL = 0b1000_0000_0000_0000;
        const STDCALL = 0b1_0000_0000_0000_0000;
        const THISCALL = 0b10_0000_0000_0000_0000;
        const VECTORCALL = 0b100_0000_0000_0000_0000;
    }
}

impl ToString for Specifier {
    fn to_string(&self) -> String {
        bitflags_to_str!(
            self,
            Self,
            TYPEDEF,
            "typedef",
            INLINE,
            "inline",
            VIRTUAL,
            "virtual",
            EXPLICIT,
            "explicit",
            FRIEND,
            "friend",
            CONSTEVAL,
            "consteval",
            CONSTEXPR,
            "constexpr",
            CONSTINIT,
            "constinit",
            REGISTER,
            "register",
            STATIC,
            "static",
            THREAD_LOCAL,
            "thread_local",
            EXTERN,
            "extern",
            MUTABLE,
            "mutable",
            CDECL,
            "__cdecl",
            CLRCALL,
            "__clrcall",
            FASTCALL,
            "__fastcall",
            STDCALL,
            "__stdcall",
            THISCALL,
            "__thiscall",
            VECTORCALL,
            "__vectorcall"
        )
    }
}

impl Dump for Specifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

impl Specifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Typedef => {
                *self |= Specifier::TYPEDEF;
                true
            }
            Token::Inline => {
                *self |= Specifier::INLINE;
                true
            }
            Token::Virtual => {
                *self |= Specifier::VIRTUAL;
                true
            }
            Token::Explicit => {
                *self |= Specifier::EXPLICIT;
                true
            }
            Token::Friend => {
                *self |= Specifier::FRIEND;
                true
            }
            Token::Consteval => {
                *self |= Specifier::CONSTEVAL;
                true
            }
            Token::Constexpr => {
                *self |= Specifier::CONSTEXPR;
                true
            }
            Token::Constinit => {
                *self |= Specifier::CONSTINIT;
                true
            }
            Token::Register => {
                *self |= Specifier::REGISTER;
                true
            }
            Token::Static => {
                *self |= Specifier::STATIC;
                true
            }
            Token::ThreadLocal => {
                *self |= Specifier::THREAD_LOCAL;
                true
            }
            Token::Extern => {
                *self |= Specifier::EXTERN;
                true
            }
            Token::Mutable => {
                *self |= Specifier::MUTABLE;
                true
            }
            Token::Cdecl => {
                *self |= Specifier::CDECL;
                true
            }
            Token::Clrcall => {
                *self |= Specifier::CLRCALL;
                true
            }
            Token::Fastcall => {
                *self |= Specifier::FASTCALL;
                true
            }
            Token::Stdcall => {
                *self |= Specifier::STDCALL;
                true
            }
            Token::Thiscall => {
                *self |= Specifier::THISCALL;
                true
            }
            Token::Vectorcall => {
                *self |= Specifier::VECTORCALL;
                true
            }
            _ => false,
        }
    }

    pub(crate) fn is_specifier(tok: &Token) -> bool {
        match tok {
            Token::Typedef
            | Token::Inline
            | Token::Virtual
            | Token::Explicit
            | Token::Friend
            | Token::Consteval
            | Token::Constexpr
            | Token::Constinit
            | Token::Register
            | Token::Static
            | Token::ThreadLocal
            | Token::Extern
            | Token::Mutable
            | Token::Cdecl
            | Token::Clrcall
            | Token::Fastcall
            | Token::Stdcall
            | Token::Thiscall
            | Token::Vectorcall => true,
            _ => false,
        }
    }
}
