// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expressions::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Do {
    pub attributes: Option<Attributes>,
    pub body: Statement,
    pub condition: ExprNode,
}

pub struct DoStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DoStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<LocToken>, Option<Do>) {
        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::While {
            unreachable!("While expected after body in do statement");
        }

        let tok = self.lexer.next_useful();
        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in do statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::RightParen {
            unreachable!("Invalid token in do statements: {:?}", tok);
        }

        let tok = self.lexer.next_useful();
        match tok.tok {
            Token::SemiColon => (
                None,
                Some(Do {
                    attributes,
                    body: body.unwrap(),
                    condition: condition.unwrap(),
                }),
            ),
            _ => {
                unreachable!("Invalid token in return statements: {:?}", tok);
            }
        }
    }
}
