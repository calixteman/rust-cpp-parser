use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExprNode, ExpressionParser, Parameters, ParametersParser};

#[derive(Clone, Debug, PartialEq)]
pub enum Initializer {
    Equal(ExprNode),
    Paren(Parameters),
    Brace(Parameters),
}

pub struct InitializerParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> InitializerParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Initializer>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok.tok {
            Token::Equal => {
                let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
                let (tok, expr) = ep.parse(None);
                (tok, Some(Initializer::Equal(expr.unwrap())))
            }
            Token::LeftParen => {
                let pp = ParametersParser::new(self.lexer, Token::RightParen);
                let (tok, params) = pp.parse(None);
                (tok, Some(Initializer::Paren(params.unwrap())))
            }
            Token::LeftBrace => {
                let pp = ParametersParser::new(self.lexer, Token::RightBrace);
                let (tok, params) = pp.parse(None);
                (tok, Some(Initializer::Brace(params.unwrap())))
            }
            _ => (Some(tok), None),
        }
    }
}
