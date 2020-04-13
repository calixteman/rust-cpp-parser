use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken};
use crate::parser::attributes::{Attributes, AttributesParser};

use super::decl::{Declarator, DeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Reference {
    pub(crate) decl: Box<Declarator>,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) lvalue: bool,
}

impl Reference {
    pub fn decl(&self) -> &Declarator {
        &self.decl
    }

    pub fn is_lvalue(&self) -> bool {
        self.lvalue
    }
}

pub struct ReferenceDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    lvalue: bool,
}

impl<'a, 'b, PC: PreprocContext> ReferenceDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>, lvalue: bool) -> Self {
        Self { lexer, lvalue }
    }

    pub(super) fn parse(self) -> (Option<LocToken<'a>>, Reference) {
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(None);

        let dp = DeclaratorParser::new(self.lexer);
        let (tok, decl) = dp.parse(tok);
        let reference = Reference {
            decl: Box::new(decl.unwrap()),
            attributes,
            lvalue: self.lvalue,
        };

        (tok, reference)
    }
}
