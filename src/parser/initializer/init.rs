// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use crate::lexer::{TLexer, Token};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{
    ExprNode, ExpressionParser, ListInitialization, ListInitializationParser, Parameters,
    ParametersParser,
};
use crate::parser::Context;

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

pub struct InitializerParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> InitializerParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Initializer>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok {
            Token::Equal => {
                let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
                let (tok, expr) = ep.parse(None, context)?;
                Ok((tok, Some(Initializer::Equal(expr.unwrap()))))
            }
            Token::LeftParen => {
                let pp = ParametersParser::new(self.lexer, Token::RightParen);
                let (tok, params) = pp.parse(None, None, context)?;
                Ok((tok, Some(Initializer::Paren(params.unwrap()))))
            }
            Token::LeftBrace => {
                let lip = ListInitializationParser::new(self.lexer);
                let (tok, params) = lip.parse(Some(tok), context)?;
                Ok((tok, Some(Initializer::Brace(params.unwrap()))))
            }
            _ => Ok((Some(tok), None)),
        }
    }
}
