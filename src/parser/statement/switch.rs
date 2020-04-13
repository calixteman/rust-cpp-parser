use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expression::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Switch {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) condition: ExprNode,
    pub(crate) cases: Box<Statement>,
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
    ) -> (Option<LocToken<'a>>, Option<Switch>) {
        let tok = self.lexer.next_useful();
        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in switch statement: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        if let Some(tok) = tok {
            if tok.tok != Token::RightParen {
                unreachable!("Invalid token in switch statement: {:?}", tok);
            }
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, cases) = sp.parse(None);

        (
            tok,
            Some(Switch {
                attributes,
                condition: condition.unwrap(),
                cases: Box::new(cases.unwrap()),
            }),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Case {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) value: ExprNode,
    pub(crate) then: Box<Statement>,
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
    ) -> (Option<LocToken<'a>>, Option<Case>) {
        let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
        let (tok, value) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::Colon {
            unreachable!("Invalid token in case statement: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, then) = sp.parse(None);

        (
            tok,
            Some(Case {
                attributes,
                value: value.unwrap(),
                then: Box::new(then.unwrap()),
            }),
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Default {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) then: Box<Statement>,
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
    ) -> (Option<LocToken<'a>>, Option<Default>) {
        let tok = self.lexer.next_useful();
        if tok.tok != Token::Colon {
            unreachable!("Invalid token in case statement: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, then) = sp.parse(None);

        (
            tok,
            Some(Default {
                attributes,
                then: Box::new(then.unwrap()),
            }),
        )
    }
}
