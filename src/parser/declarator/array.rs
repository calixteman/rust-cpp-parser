use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::expression::{ExpressionParser, Node, Parameters, ParametersParser};
use crate::parser::name::Qualified;

use super::super::r#type::{CVQualifier, Type};
use super::decl::{DeclarationParser, Declarator, DeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    pub(crate) identifier: Option<Qualified>,
    pub(crate) id_attributes: Option<Attributes>,
    pub(crate) size: Option<Node>,
    pub(crate) attributes: Option<Attributes>,
}

pub struct ArrayParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ArrayParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken<'a>>) -> (Option<LocToken<'a>>, Option<Array>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftBrack {
            return (Some(tok), None);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::RightBrack);
        let (tok, expr) = ep.parse(None);

        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        let array = Array {
            identifier: None,
            id_attributes: None,
            size: expr,
            attributes,
        };

        (tok, Some(array))
    }
}
