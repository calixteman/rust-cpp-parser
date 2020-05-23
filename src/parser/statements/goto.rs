// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use crate::lexer::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::dump::Dump;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub enum Label {
    Id(String),
    Expr(ExprNode),
}

impl Dump for Label {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        match self {
            Self::Id(l) => l.dump(name, prefix, last, stdout),
            Self::Expr(l) => l.dump(name, prefix, last, stdout),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Goto {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) label: Label,
}

impl Dump for Goto {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "goto", prefix, last, stdout, attributes, label);
    }
}

pub struct GotoStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> GotoStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Goto>) {
        let tok = self.lexer.next_useful();

        match tok {
            Token::Identifier(id) => (
                None,
                Some(Goto {
                    attributes,
                    label: Label::Id(id),
                }),
            ),
            Token::Star => {
                let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                let (tok, expr) = ep.parse(Some(tok), context);

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
