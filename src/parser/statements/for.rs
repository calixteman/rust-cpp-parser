// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::lexer::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::declarations::{DeclOrExpr, DeclOrExprParser, TypeDeclarator};
use crate::parser::dump::Dump;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::{Context, ScopeKind};

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
    pub decl: Rc<TypeDeclarator>,
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

pub struct ForStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ForStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<ForRes>) {
        let tok = self.lexer.next_useful();

        if tok != Token::LeftParen {
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        context.set_current(None, ScopeKind::ForBlock);

        let dep = DeclOrExprParser::new(self.lexer);
        let (tok, init) = dep.parse(None, context);

        if let Some(DeclOrExpr::Decl(typ)) = init.as_ref() {
            context.add_type_decl(Rc::clone(typ));
        }

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::Colon {
            // for (decl : ...)
            let decl = if let DeclOrExpr::Decl(typ) = init.unwrap() {
                context.add_type_decl(Rc::clone(&typ));
                typ
            } else {
                context.pop();
                unreachable!("Invalid expression in for statement");
            };

            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            let (tok, expr) = ep.parse(None, context);

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                context.pop();
                unreachable!("Invalid token in for statements: {:?}", tok);
            }

            let sp = StatementParser::new(self.lexer);
            let (tok, body) = sp.parse(None, context);
            context.pop();

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
            context.pop();
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let dep = DeclOrExprParser::new(self.lexer);
        let (tok, condition) = dep.parse(None, context);

        if let Some(DeclOrExpr::Decl(typ)) = condition.as_ref() {
            context.add_type_decl(Rc::clone(typ));
        }

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::Colon {
            // for (init; decl : ...)
            let decl = if let DeclOrExpr::Decl(typ) = condition.unwrap() {
                typ
            } else {
                context.pop();
                unreachable!("Invalid expression in for statement");
            };

            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            let (tok, expr) = ep.parse(None, context);

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                context.pop();
                unreachable!("Invalid token in for statements: {:?}", tok);
            }

            let sp = StatementParser::new(self.lexer);
            let (tok, body) = sp.parse(None, context);
            context.pop();

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
                context.pop();
                unreachable!("Invalid expression in for statement");
            }
        } else {
            None
        };

        if tok != Token::SemiColon {
            context.pop();
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (tok, iteration) = ep.parse(None, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            context.pop();
            unreachable!("Invalid token in for statements: {:?}", tok);
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None, context);
        context.pop();

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
