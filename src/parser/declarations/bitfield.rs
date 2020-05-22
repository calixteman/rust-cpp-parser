// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::TypeDeclarator;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};
use crate::parser::expressions::Operator;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::initializer::Initializer;
use crate::parser::Context;

pub struct BitFieldDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> BitFieldDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        typ: &mut TypeDeclarator,
        context: &mut Context,
    ) -> Option<Token> {
        let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
        let (tok, size) = ep.parse(tok, context);

        let size = if let Some(size) = size {
            size
        } else {
            unreachable!("Invalid bitfield size");
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

        tok
    }
}
