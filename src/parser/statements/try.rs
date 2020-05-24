// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::lexer::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::declarations::{TypeDeclarator, TypeDeclaratorParser};
use crate::parser::dump::Dump;
use crate::parser::{Context, ScopeKind};

#[derive(Clone, Debug, PartialEq)]
pub struct Try {
    pub attributes: Option<Attributes>,
    pub body: Box<Statement>,
    pub clause: Option<Rc<TypeDeclarator>>,
    pub handler: Box<Statement>,
}

impl Dump for Try {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "try", prefix, last, stdout, attributes, body, clause, handler);
    }
}

pub struct TryStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> TryStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Try>) {
        let sp = StatementParser::new(self.lexer);
        let (tok, body) = sp.parse(None, context);

        let body = if let Some(body) = body {
            body
        } else {
            unreachable!("Invalid token in try: {:?}", tok);
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Catch {
            unreachable!("Catch expected after body in try statement");
        }

        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            unreachable!("Invalid token in catch clause: {:?}", tok);
        }

        let tok = self.lexer.next_useful();
        let (tok, clause) = if tok == Token::Ellipsis {
            (None, None)
        } else {
            let tp = TypeDeclaratorParser::new(self.lexer);
            let (tok, typ) = tp.parse(Some(tok), None, false, context);

            if typ.is_some() {
                (tok, typ)
            } else {
                unreachable!("Invalid token in catch clause: {:?}", tok);
            }
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            unreachable!("Invalid token in catch clause: {:?}", tok);
        }

        // Exception handler
        let clause = if let Some(clause) = clause {
            context.set_current(None, ScopeKind::CatchBlock);
            context.add_type_decl(Rc::clone(&clause));
            Some(clause)
        } else {
            None
        };

        let sp = StatementParser::new(self.lexer);
        let (tok, handler) = sp.parse(None, context);

        if clause.is_some() {
            context.pop();
        }

        let handler = if let Some(handler) = handler {
            handler
        } else {
            unreachable!("Invalid token in try handler: {:?}", tok);
        };

        (
            tok,
            Some(Try {
                attributes,
                body: Box::new(body),
                clause,
                handler: Box::new(handler),
            }),
        )
    }
}
