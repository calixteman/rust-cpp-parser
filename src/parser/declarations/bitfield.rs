// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::TypeDeclarator;
use crate::lexer::{TLexer, Token};
use crate::parser::errors::ParserError;
use crate::parser::expressions::Operator;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::initializer::Initializer;
use crate::parser::Context;

pub struct BitFieldDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> BitFieldDeclaratorParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        typ: &mut TypeDeclarator,
        context: &mut Context,
    ) -> Result<Option<Token>, ParserError> {
        let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
        let (tok, size) = ep.parse(tok, context)?;

        let size = if let Some(size) = size {
            size
        } else {
            return Err(ParserError::InvalidBitfieldSize {
                sp: self.lexer.span(),
            });
        };

        let (size, init) = match size {
            ExprNode::BinaryOp(operation) => {
                if operation.op == Operator::Assign {
                    (operation.arg1, Some(Initializer::Equal(operation.arg2)))
                } else {
                    (ExprNode::BinaryOp(operation), None)
                }
            }
            ExprNode::InitExpr(init) => (init.base, Some(Initializer::Brace(init.list))),
            _ => (size, None),
        };

        typ.init = init;
        typ.bitfield_size = Some(size);

        Ok(tok)
    }
}
