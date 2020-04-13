use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expression::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Do {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) body: Box<Statement>,
    pub(crate) condition: ExprNode,
}

pub struct DoStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DoStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
    ) -> (Option<LocToken<'a>>, Option<Do>) {
        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::While {
            unreachable!("While expected after body in do statement");
        }

        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in do statement: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::RightParen {
            unreachable!("Invalid token in do statement: {:?}", tok);
        }

        let tok = self.lexer.next_useful();
        match tok.tok {
            Token::SemiColon => (
                None,
                Some(Do {
                    attributes,
                    body: Box::new(body.unwrap()),
                    condition: condition.unwrap(),
                }),
            ),
            _ => {
                unreachable!("Invalid token in return statement: {:?}", tok);
            }
        }
    }
}
