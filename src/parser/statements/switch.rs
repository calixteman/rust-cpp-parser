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
pub struct Switch {
    pub attributes: Option<Attributes>,
    pub condition: ExprNode,
    pub cases: Statement,
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
    ) -> (Option<LocToken>, Option<Switch>) {
        let tok = self.lexer.next_useful();
        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in switch statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        if let Some(tok) = tok {
            if tok.tok != Token::RightParen {
                unreachable!("Invalid token in switch statements: {:?}", tok);
            }
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, cases) = sp.parse(None);

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

pub struct CaseStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> CaseStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<LocToken>, Option<Case>) {
        let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
        let (tok, value) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::Colon {
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
    ) -> (Option<LocToken>, Option<Default>) {
        let tok = self.lexer.next_useful();
        if tok.tok != Token::Colon {
            unreachable!("Invalid token in case statements: {:?}", tok);
        }

        (None, Some(Default { attributes }))
    }
}
