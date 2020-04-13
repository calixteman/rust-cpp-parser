use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken};
use crate::parser::attributes::{Attributes, AttributesParser};

use super::super::r#type::CVQualifier;
use super::decl::{Declarator, DeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Pointer {
    pub(crate) decl: Box<Declarator>,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) cv: CVQualifier,
}

impl Pointer {
    pub fn decl(&self) -> &Declarator {
        &self.decl
    }

    pub fn is_const(&self) -> bool {
        self.cv.intersects(CVQualifier::CONST)
    }

    pub fn is_volatile(&self) -> bool {
        self.cv.intersects(CVQualifier::VOLATILE)
    }
}

pub struct PointerDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> PointerDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self) -> (Option<LocToken<'a>>, Pointer) {
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(None);
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let mut cv = CVQualifier::empty();

        loop {
            if !cv.from_tok(&tok.tok) {
                break;
            }

            tok = self.lexer.next_useful();
        }

        let dp = DeclaratorParser::new(self.lexer);
        let (tok, decl) = dp.parse(Some(tok));
        let ptr = Pointer {
            decl: Box::new(decl.unwrap()),
            attributes,
            cv,
        };

        (tok, ptr)
    }
}
