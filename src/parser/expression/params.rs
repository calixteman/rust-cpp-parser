// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExprNode, ExpressionParser};

pub type Parameters = Vec<Option<ExprNode>>;

pub(crate) struct ParametersParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    term: Token,
}

impl<'a, 'b, PC: PreprocContext> ParametersParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>, term: Token) -> Self {
        Self { lexer, term }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        first: Option<ExprNode>,
    ) -> (Option<LocToken>, Option<Parameters>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (mut tok, mut params) = if let Some(first) = first {
            let tok = if tok.tok == Token::Comma {
                self.lexer.next_useful()
            } else {
                tok
            };
            (tok, vec![Some(first)])
        } else {
            (tok, Vec::new())
        };

        if tok.tok == self.term {
            return (None, Some(params));
        }

        loop {
            let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
            let (tk, expr) = ep.parse(Some(tok));

            params.push(expr);

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());

            match tk.tok {
                Token::Comma => {}
                _ => {
                    if tk.tok == self.term {
                        return (None, Some(params));
                    } else {
                        unreachable!("Invalid token in params: {:?}", tk);
                    }
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}
