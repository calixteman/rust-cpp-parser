// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::context::Context;
use super::declarations::{DeclarationListParser, Declarations};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, TLexer, Token};

#[derive(Clone, Debug, PartialEq)]
pub struct Unit {
    decls: Declarations,
}

pub struct UnitParser<'a, PC: PreprocContext> {
    buf: &'a [u8],
    lexer: Lexer<'a, PC>,
    context: Context,
}

impl<'a, PC: PreprocContext> UnitParser<'a, PC> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            lexer: Lexer::new(buf),
            context: Context::default(),
        }
    }

    pub fn parse(&mut self) -> Unit {
        let dlp = DeclarationListParser::new(&mut self.lexer);
        let (tok, decls) = dlp.parse(None, &mut self.context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Eof {
            unreachable!("Invalid token in unit: {:?}")
        }

        Unit {
            decls: decls.unwrap(),
        }
    }
}
