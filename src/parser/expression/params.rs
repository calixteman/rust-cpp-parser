use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExpressionParser, Node};

pub type Parameters = Vec<Option<Node>>;

pub struct ParametersParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    params: Parameters,
    term: Token<'a>,
}

impl<'a, 'b, PC: PreprocContext> ParametersParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>, term: Token<'a>) -> Self {
        Self {
            lexer,
            params: Vec::new(),
            term,
        }
    }

    pub(crate) fn parse(
        mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Parameters>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok.tok == self.term {
            return (None, Some(self.params));
        }

        loop {
            let mut ep = ExpressionParser::new(&mut self.lexer, self.term);
            let (tk, expr) = ep.parse(Some(tok));

            self.params.push(expr);

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());

            match tk.tok {
                Token::Comma => {}
                _ => {
                    if tk.tok == self.term {
                        return (None, Some(self.params));
                    } else {
                        unreachable!("Invalid token in qualified name: {:?}", tk);
                    }
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}
