// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::lexer::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
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

pub struct IfStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> IfStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<If>), ParserError> {
        let mut tok = self.lexer.next_useful();
        let constexpr = if tok == Token::Constexpr {
            tok = self.lexer.next_useful();
            true
        } else {
            false
        };

        if tok != Token::LeftParen {
            return Err(ParserError::InvalidTokenInIf {
                sp: self.lexer.span(),
                tok,
            });
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, condition) = ep.parse(None, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            return Err(ParserError::InvalidTokenInIf {
                sp: self.lexer.span(),
                tok,
            });
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, then) = sp.parse(None, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, r#else) = if tok == Token::Else {
            let sp = StatementParser::new(self.lexer);
            sp.parse(None, context)?
        } else {
            (Some(tok), None)
        };

        Ok((
            tok,
            Some(If {
                attributes,
                constexpr,
                condition: condition.unwrap(),
                then: then.unwrap(),
                r#else,
            }),
        ))
    }
}
