// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expressions::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub enum Label {
    Id(String),
    Expr(ExprNode),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Goto {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) label: Label,
}

pub struct GotoStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> GotoStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<LocToken>, Option<Goto>) {
        let tok = self.lexer.next_useful();

        match tok.tok {
            Token::Identifier(id) => (
                None,
                Some(Goto {
                    attributes,
                    label: Label::Id(id),
                }),
            ),
            Token::Star => {
                let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                let (tok, expr) = ep.parse(None);

                (
                    tok,
                    Some(Goto {
                        attributes,
                        label: Label::Expr(expr.unwrap()),
                    }),
                )
            }
            _ => {
                unreachable!("Invalid token in goto statements: {:?}", tok);
            }
        }
    }
}
