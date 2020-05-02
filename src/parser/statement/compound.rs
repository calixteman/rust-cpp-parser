// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;

#[derive(Clone, Debug, PartialEq)]
pub struct Compound {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) stmts: Vec<Statement>,
}

pub struct CompoundStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> CompoundStmtParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        attributes: Option<Attributes>,
    ) -> (Option<LocToken>, Option<Compound>) {
        let mut stmts = Vec::new();
        let mut tok = self.lexer.next_useful();

        loop {
            if tok.tok == Token::RightBrace {
                return (None, Some(Compound { attributes, stmts }));
            }

            let sp = StatementParser::new(self.lexer);
            let (tk, stmt) = sp.parse(Some(tok));

            if let Some(stmt) = stmt {
                stmts.push(stmt);
            }

            tok = tk.unwrap_or_else(|| self.lexer.next_useful());
        }
    }
}
