// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::expression::{ExprNode, ExpressionParser};
use crate::parser::r#type::Type;

#[derive(Clone, Debug, PartialEq)]
pub struct Dimension {
    pub size: Option<ExprNode>,
    pub attributes: Option<Attributes>,
}

pub type Dimensions = Vec<Dimension>;

#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    pub base: Option<Type>,
    pub dimensions: Dimensions,
}

pub struct ArrayParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ArrayParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Array>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut dimensions = Vec::new();

        loop {
            if tok.tok != Token::LeftBrack {
                break;
            }

            let mut ep = ExpressionParser::new(self.lexer, Token::RightBrack);
            let (tk, size) = ep.parse(None);

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            if tk.tok != Token::RightBrack {
                unreachable!("Invalid array size delimiter: {:?}", tk);
            }

            let ap = AttributesParser::new(self.lexer);
            let (tk, attributes) = ap.parse(None);

            tok = tk.unwrap_or_else(|| self.lexer.next_useful());

            dimensions.push(Dimension { size, attributes });
        }

        if dimensions.is_empty() {
            (Some(tok), None)
        } else {
            (
                Some(tok),
                Some(Array {
                    base: None,
                    dimensions,
                }),
            )
        }
    }
}
