use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

use super::super::r#type::CVQualifier;

use super::decl::{Declarator, DeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Pointer {
    pub(crate) decl: Box<Declarator>,
    pub(crate) cv: CVQualifier,
}

impl Pointer {
    pub fn decl(&self) -> &Box<Declarator> {
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
    cv: CVQualifier,
}

impl<'a, 'b, PC: PreprocContext> PointerDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            cv: CVQualifier::empty(),
        }
    }

    pub(super) fn parse(mut self) -> (Option<LocToken<'a>>, Pointer) {
        let tok = loop {
            let tok = self.lexer.next_useful();
            if self.cv.from_tok(&tok.tok) {
                continue;
            }

            break tok;
        };

        let dp = DeclaratorParser::new(self.lexer);
        let (tok, decl) = dp.parse(tok);
        let ptr = Pointer {
            decl: Box::new(decl.unwrap()),
            cv: self.cv,
        };

        (tok, ptr)
    }
}
