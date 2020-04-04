use super::ast::{Node};
use crate::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use super::type_qualifier::{Qualifier, TypeQualParser};

pub struct TopLevel<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> TopLevel<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
        }
    }

    fn parse(&mut self) -> Node {
        loop {
            let tok = self.lexer.next_useful();
            if let Some(qual) = Qualifier::from_tok(tok.tok) {
                let tqp = TypeQualParser::new(&mut self.lexer, qual);
                let (tok, quals) = tqp.parse();
            }
        }
    }
}
