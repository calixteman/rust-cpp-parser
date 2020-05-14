// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::dump_obj;
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::dump::Dump;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub attributes: Option<Attributes>,
    pub constexpr: bool,
    pub condition: ExprNode,
    pub then: Statement,
    pub r#else: Option<Statement>,
}

impl Dump for If {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self, name, "if", prefix, last, stdout, attributes, constexpr, condition, then, r#else
        );
    }
}

pub struct IfStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> IfStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<If>) {
        let mut tok = self.lexer.next_useful();
        let constexpr = if tok == Token::Constexpr {
            tok = self.lexer.next_useful();
            true
        } else {
            false
        };

        if tok != Token::LeftParen {
            unreachable!("Invalid token in if statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            unreachable!("Invalid token in if statements: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, then) = sp.parse(None, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, r#else) = if tok == Token::Else {
            let sp = StatementParser::new(self.lexer);
            sp.parse(None, context)
        } else {
            (Some(tok), None)
        };

        (
            tok,
            Some(If {
                attributes,
                constexpr,
                condition: condition.unwrap(),
                then: then.unwrap(),
                r#else,
            }),
        )
    }
}
