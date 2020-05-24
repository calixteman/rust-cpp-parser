// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{TLexer, Token};
use crate::parser::errors::ParserError;
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
    ) -> Result<(Option<Token>, Option<Destructor>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Tilde {
            return Ok((Some(tok), None));
        }

        let tok = self.lexer.next_useful();
        if let Token::Identifier(name) = tok {
            Ok((None, Some(Destructor { name })))
        } else {
            Err(ParserError::InvalidTokenInDtor {
                sp: self.lexer.span(),
                tok,
            })
        }
    }
}
