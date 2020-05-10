// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::declarations::{DeclOrExpr, DeclOrExprParser, TypeDeclarator};
use crate::parser::expressions::{ExprNode, ExpressionParser};

use crate::dump_obj;
use crate::parser::dump::Dump;
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub struct For {
    pub attributes: Option<Attributes>,
    pub init: Option<DeclOrExpr>,
    pub condition: Option<ExprNode>,
    pub iteration: Option<ExprNode>,
    pub body: Statement,
}

impl Dump for For {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self, name, "for", prefix, last, stdout, attributes, init, condition, iteration, body
        );
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ForRange {
    pub attributes: Option<Attributes>,
    pub init: Option<DeclOrExpr>,
    pub decl: TypeDeclarator,
    pub expr: ExprNode,
    pub body: Statement,
}

impl Dump for ForRange {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "for-range",
            prefix,
            last,
            stdout,
            attributes,
            init,
            decl,
            expr,
            body
        );
    }
}

pub(super) enum ForRes {
    Normal(For),
    Range(ForRange),
}

pub struct ForStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ForStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, attributes: Option<Attributes>) -> (Option<Token>, Option<ForRes>) {
        let tok = self.lexer.next_useful();

        if tok != Token::LeftParen {
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let dep = DeclOrExprParser::new(self.lexer);
        let (tok, init) = dep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::Colon {
            // for (decl : ...)
            let decl = if let DeclOrExpr::Decl(typ) = init.unwrap() {
                typ
            } else {
                unreachable!("Invalid expression in for statement");
            };

            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            let (tok, expr) = ep.parse(None);

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                unreachable!("Invalid token in for statements: {:?}", tok);
            }

            let sp = StatementParser::new(self.lexer);
            let (tok, body) = sp.parse(None);

            return (
                tok,
                Some(ForRes::Range(ForRange {
                    attributes,
                    init: None,
                    decl,
                    expr: expr.unwrap(),
                    body: body.unwrap(),
                })),
            );
        }

        if tok != Token::SemiColon {
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let dep = DeclOrExprParser::new(self.lexer);
        let (tok, condition) = dep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::Colon {
            // for (init; decl : ...)
            let decl = if let DeclOrExpr::Decl(typ) = condition.unwrap() {
                typ
            } else {
                unreachable!("Invalid expression in for statement");
            };

            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            let (tok, expr) = ep.parse(None);

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                unreachable!("Invalid token in for statements: {:?}", tok);
            }

            let sp = StatementParser::new(self.lexer);
            let (tok, body) = sp.parse(None);

            return (
                tok,
                Some(ForRes::Range(ForRange {
                    attributes,
                    init,
                    decl,
                    expr: expr.unwrap(),
                    body: body.unwrap(),
                })),
            );
        }

        // we're in a classic for loop so the condition is an expression
        let condition = if let Some(cond) = condition {
            if let DeclOrExpr::Expr(cond) = cond {
                Some(cond)
            } else {
                unreachable!("Invalid expression in for statement");
            }
        } else {
            None
        };

        if tok != Token::SemiColon {
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, iteration) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None);

        (
            tok,
            Some(ForRes::Normal(For {
                attributes,
                init,
                condition,
                iteration,
                body: body.unwrap(),
            })),
        )
    }
}
