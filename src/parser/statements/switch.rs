// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::{Statement, StatementParser};
use crate::lexer::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::declarations::{DeclOrExpr, DeclOrExprParser};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::{Context, ScopeKind};

#[derive(Clone, Debug, PartialEq)]
pub struct Switch {
    pub attributes: Option<Attributes>,
    pub condition: DeclOrExpr,
    pub cases: Statement,
}

impl Dump for Switch {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "switch", prefix, last, stdout, attributes, condition, cases);
    }
}

pub struct SwitchStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> SwitchStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Switch>), ParserError> {
        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            return Err(ParserError::InvalidTokenInSwitch {
                sp: self.lexer.span(),
                tok,
            });
        }

        context.set_current(None, ScopeKind::SwitchBlock);

        let dep = DeclOrExprParser::new(self.lexer);
        let (tok, condition) = dep.parse(None, context)?;

        if let Some(DeclOrExpr::Decl(typ)) = condition.as_ref() {
            context.add_type_decl(Rc::clone(typ));
        }

        if let Some(tok) = tok {
            if tok != Token::RightParen {
                context.pop();
                return Err(ParserError::InvalidTokenInSwitch {
                    sp: self.lexer.span(),
                    tok,
                });
            }
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, cases) = sp.parse(None, context)?;
        context.pop();

        Ok((
            tok,
            Some(Switch {
                attributes,
                condition: condition.unwrap(),
                cases: cases.unwrap(),
            }),
        ))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Case {
    pub attributes: Option<Attributes>,
    pub value: ExprNode,
}

impl Dump for Case {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "case", prefix, last, stdout, attributes, value);
    }
}

pub struct CaseStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> CaseStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Case>), ParserError> {
        let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
        let (tok, value) = ep.parse(None, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Colon {
            return Err(ParserError::InvalidTokenInSwitch {
                sp: self.lexer.span(),
                tok,
            });
        }

        Ok((
            None,
            Some(Case {
                attributes,
                value: value.unwrap(),
            }),
        ))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Default {
    pub attributes: Option<Attributes>,
}

impl Dump for Default {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "default", prefix, last, stdout, attributes);
    }
}

pub struct DefaultStmtParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> DefaultStmtParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
        _context: &mut Context,
    ) -> Result<(Option<Token>, Option<Default>), ParserError> {
        let tok = self.lexer.next_useful();
        if tok != Token::Colon {
            return Err(ParserError::InvalidTokenInSwitch {
                sp: self.lexer.span(),
                tok,
            });
        }

        Ok((None, Some(Default { attributes })))
    }
}
