use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExpressionParser, Node};

pub type Parameters = Vec<Option<Node>>;

pub struct ParametersParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    term: Token<'a>,
}

impl<'a, 'b, PC: PreprocContext> ParametersParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>, term: Token<'a>) -> Self {
        Self { lexer, term }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Parameters>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut params = Vec::new();

        if tok.tok == self.term {
            return (None, Some(params));
        }

        loop {
            let mut ep = ExpressionParser::new(self.lexer, self.term.clone());
            let (tk, expr) = ep.parse(Some(tok));

            params.push(expr);

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());

            match tk.tok {
                Token::Comma => {}
                _ => {
                    if tk.tok == self.term {
                        return (None, Some(params));
                    } else {
                        unreachable!("Invalid token in qualified name: {:?}", tk);
                    }
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}
