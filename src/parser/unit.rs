// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::context::Context;
use super::declarations::{DeclarationListParser, Declarations};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, TLexer, Token};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;

#[derive(Clone, Debug, PartialEq)]
pub struct Unit {
    decls: Declarations,
}

impl Dump for Unit {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "unit", prefix, last, stdout, decls);
    }
}

pub struct UnitParser<'a, PC: PreprocContext> {
    pub lexer: Lexer<'a, PC>,
    pub context: Context,
}

impl<'a, PC: PreprocContext> UnitParser<'a, PC> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            lexer: Lexer::new(buf),
            context: Context::default(),
        }
    }

    pub fn parse(&mut self) -> Result<Unit, ParserError> {
        let dlp = DeclarationListParser::new(&mut self.lexer);
        let (tok, decls) = dlp.parse(None, &mut self.context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Eof {
            return Err(ParserError::InvalidTokenInUnit {
                sp: self.lexer.span(),
                tok,
            });
        }

        Ok(Unit {
            decls: decls.unwrap(),
        })
    }
}
