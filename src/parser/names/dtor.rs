// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};

#[derive(Clone, Debug, PartialEq)]
pub struct Destructor {
    pub name: String,
}

pub(crate) struct DtorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DtorParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<Destructor>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Tilde {
            return (Some(tok), None);
        }

        let tok = self.lexer.next_useful();
        if let Token::Identifier(name) = tok {
            (None, Some(Destructor { name }))
        } else {
            unreachable!("Invalid token in dtor name: {:?}", tok)
        }
    }
}
