// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};
use crate::parser::expressions::{
    ExprNode, ExpressionParser, ListInitialization, ListInitializationParser, Parameters,
    ParametersParser,
};

use crate::parser::dump::Dump;
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Equal(ExprNode),
    Paren(Parameters),
    Brace(ListInitialization),
}

impl Dump for Initializer {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::Equal(x) => dump!(x),
            Self::Paren(x) => dump!(x),
            Self::Brace(x) => dump!(x),
        }
    }
}

pub struct InitializerParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> InitializerParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<Initializer>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok {
            Token::Equal => {
                let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
                let (tok, expr) = ep.parse(None);
                (tok, Some(Initializer::Equal(expr.unwrap())))
            }
            Token::LeftParen => {
                let pp = ParametersParser::new(self.lexer, Token::RightParen);
                let (tok, params) = pp.parse(None, None);
                (tok, Some(Initializer::Paren(params.unwrap())))
            }
            Token::LeftBrace => {
                let lip = ListInitializationParser::new(self.lexer);
                let (tok, params) = lip.parse(Some(tok));
                (tok, Some(Initializer::Brace(params.unwrap())))
            }
            _ => (Some(tok), None),
        }
    }
}
