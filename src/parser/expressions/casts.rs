// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use crate::lexer::{TLexer, Token};
use crate::parser::declarations::TypeDeclaratorParser;
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::types::Type;
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct StaticCast {
    pub typ: Type,
    pub arg: ExprNode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct DynamicCast {
    pub typ: Type,
    pub arg: ExprNode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ConstCast {
    pub typ: Type,
    pub arg: ExprNode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ReinterpretCast {
    pub typ: Type,
    pub arg: ExprNode,
}

impl Dump for StaticCast {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "static_cast", prefix, last, stdout, typ, arg);
    }
}

impl Dump for DynamicCast {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "dynamic_cast", prefix, last, stdout, typ, arg);
    }
}

impl Dump for ConstCast {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "const_cast", prefix, last, stdout, typ, arg);
    }
}

impl Dump for ReinterpretCast {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "reinterpret_cast",
            prefix,
            last,
            stdout,
            typ,
            arg
        );
    }
}

pub(crate) struct FooCastParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> FooCastParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        base_tok: Token,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<ExprNode>), ParserError> {
        let tok = self.lexer.next_useful();
        if tok != Token::Lower {
            return Err(ParserError::InvalidTokenInExpr {
                sp: self.lexer.span(),
                tok,
            });
        }

        let tdp = TypeDeclaratorParser::new(self.lexer);
        let (tok, typ) = tdp.parse(None, None, false, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Greater {
            return Err(ParserError::InvalidTokenInExpr {
                sp: self.lexer.span(),
                tok,
            });
        }

        let typ = Rc::try_unwrap(typ.unwrap()).unwrap().typ;

        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            return Err(ParserError::InvalidTokenInExpr {
                sp: self.lexer.span(),
                tok,
            });
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
        let (_, expr) = ep.parse(None, context)?;

        let arg = expr.unwrap();

        let node = match base_tok {
            Token::StaticCast => Some(ExprNode::StaticCast(Box::new(StaticCast { typ, arg }))),
            Token::DynamicCast => Some(ExprNode::DynamicCast(Box::new(DynamicCast { typ, arg }))),
            Token::ConstCast => Some(ExprNode::ConstCast(Box::new(ConstCast { typ, arg }))),
            Token::ReinterpretCast => Some(ExprNode::ReinterpretCast(Box::new(ReinterpretCast {
                typ,
                arg,
            }))),
            _ => None,
        };

        Ok((None, node))
    }
}
