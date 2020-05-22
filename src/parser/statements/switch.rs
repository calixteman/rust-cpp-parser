// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expressions::{ExprNode, ExpressionParser};

use crate::dump_obj;
use crate::parser::dump::Dump;
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct Switch {
    pub attributes: Option<Attributes>,
    pub condition: ExprNode,
    pub cases: Statement,
}

impl Dump for Switch {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "switch", prefix, last, stdout, attributes, condition, cases);
    }
}

pub struct SwitchStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> SwitchStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Switch>) {
        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            unreachable!("Invalid token in switch statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None, context);

        if let Some(tok) = tok {
            if tok != Token::RightParen {
                unreachable!("Invalid token in switch statements: {:?}", tok);
            }
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, cases) = sp.parse(None, context);

        (
            tok,
            Some(Switch {
                attributes,
                condition: condition.unwrap(),
                cases: cases.unwrap(),
            }),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Case {
    pub attributes: Option<Attributes>,
    pub value: ExprNode,
}

impl Dump for Case {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "case", prefix, last, stdout, attributes, value);
    }
}

pub struct CaseStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> CaseStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Case>) {
        let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
        let (tok, value) = ep.parse(None, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Colon {
            unreachable!("Invalid token in case statements: {:?}", tok);
        }

        (
            None,
            Some(Case {
                attributes,
                value: value.unwrap(),
            }),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Default {
    pub attributes: Option<Attributes>,
}

impl Dump for Default {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "default", prefix, last, stdout, attributes);
    }
}

pub struct DefaultStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DefaultStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        _context: &mut Context,
    ) -> (Option<Token>, Option<Default>) {
        let tok = self.lexer.next_useful();
        if tok != Token::Colon {
            unreachable!("Invalid token in case statements: {:?}", tok);
        }

        (None, Some(Default { attributes }))
    }
}
