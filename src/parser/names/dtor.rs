// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{TLexer, Token};
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq, Hash)]
pub struct Destructor {
    pub name: String,
}

pub(crate) struct DtorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> DtorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        _context: &mut Context,
    ) -> (Option<Token>, Option<Destructor>) {
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
