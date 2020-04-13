use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;
use crate::parser::expression::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Return {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) val: Option<ExprNode>,
}

pub struct ReturnStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ReturnStmtParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        attributes: Option<Attributes>,
    ) -> (Option<LocToken<'a>>, Option<Return>) {
        let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
        let (tok, expr) = ep.parse(None);

        (
            tok,
            Some(Return {
                attributes,
                val: expr,
            }),
        )
    }
}
