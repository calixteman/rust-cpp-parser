// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expressions::{ExprNode, ExpressionParser};

use crate::dump_obj;
use crate::parser::dump::Dump;
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub struct While {
    pub attributes: Option<Attributes>,
    pub condition: ExprNode,
    pub body: Statement,
}

impl Dump for While {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "while", prefix, last, stdout, attributes, condition, body);
    }
}

pub struct WhileStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> WhileStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<Token>, Option<While>) {
        let tok = self.lexer.next_useful();

        if tok != Token::LeftParen {
            unreachable!("Invalid token in while statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            unreachable!("Invalid token in if statements: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None);

        (
            tok,
            Some(While {
                attributes,
                body: body.unwrap(),
                condition: condition.unwrap(),
            }),
        )
    }
}
