use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expression::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub attributes: Option<Attributes>,
    pub constexpr: bool,
    pub condition: ExprNode,
    pub then: Statement,
    pub r#else: Option<Statement>,
}

pub struct IfStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> IfStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<LocToken>, Option<If>) {
        let mut tok = self.lexer.next_useful();
        let constexpr = if tok.tok == Token::Constexpr {
            tok = self.lexer.next_useful();
            true
        } else {
            false
        };

        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in if statement: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::RightParen {
            unreachable!("Invalid token in if statement: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, then) = sp.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, r#else) = if tok.tok == Token::Else {
            let sp = StatementParser::new(self.lexer);
            sp.parse(None)
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
