// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use crate::lexer::{TLexer, Token};
use crate::parser::dump::Dump;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::Context;

pub type Parameters = Vec<ExprNode>;

impl Dump for Parameters {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "par", prefix, last, stdout);
    }
}

pub(crate) struct ParametersParser<'a, L: TLexer> {
    lexer: &'a mut L,
    term: Token,
}

impl<'a, L: TLexer> ParametersParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L, term: Token) -> Self {
        Self { lexer, term }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        first: Option<ExprNode>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Parameters>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (mut tok, mut params) = if let Some(first) = first {
            let tok = if tok == Token::Comma {
                self.lexer.next_useful()
            } else {
                tok
            };
            (tok, vec![first])
        } else {
            (tok, Vec::new())
        };

        if tok == self.term {
            return (None, Some(params));
        }

        loop {
            let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
            let (tk, expr) = ep.parse(Some(tok), context);

            params.push(expr.unwrap());

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());

            match tk {
                Token::Comma => {}
                _ => {
                    if tk == self.term {
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
