use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;

#[derive(Clone, Debug, PartialEq)]
pub struct Goto {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) val: String,
}

pub struct GotoStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> GotoStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
    ) -> (Option<LocToken<'a>>, Option<Goto>) {
        let tok = self.lexer.next_useful();

        match tok.tok {
            Token::Identifier(id) => (
                None,
                Some(Goto {
                    attributes,
                    val: id,
                }),
            ),
            _ => {
                unreachable!("Invalid token in goto statement: {:?}", tok);
            }
        }
    }
}
