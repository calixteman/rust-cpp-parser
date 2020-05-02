// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{Parameters, ParametersParser};

pub type ListInitialization = Parameters;

pub struct ListInitializationParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ListInitializationParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
    ) -> (Option<LocToken>, Option<ListInitialization>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok.tok != Token::LeftBrace {
            return (Some(tok), None);
        }

        let pp = ParametersParser::new(self.lexer, Token::RightBrace);
        pp.parse(None, None)
    }
}
