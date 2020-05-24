// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{TLexer, Token};
use crate::parser::errors::ParserError;
use crate::parser::expressions::{Parameters, ParametersParser};
use crate::parser::Context;

pub type ListInitialization = Parameters;

pub struct ListInitializationParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ListInitializationParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<ListInitialization>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok != Token::LeftBrace {
            return Ok((Some(tok), None));
        }

        let pp = ParametersParser::new(self.lexer, Token::RightBrace);
        pp.parse(None, None, context)
    }
}
