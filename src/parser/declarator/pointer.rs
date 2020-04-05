use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken};

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
}

impl<'a, 'b, PC: PreprocContext> PointerDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self) -> (Option<LocToken<'a>>, Pointer) {
        let mut cv = CVQualifier::empty();

        let tok = loop {
            let tok = self.lexer.next_useful();
            if cv.from_tok(&tok.tok) {
                continue;
            }

            break tok;
        };

        let dp = DeclaratorParser::new(self.lexer);
        let (tok, decl) = dp.parse(tok);
        let ptr = Pointer {
            decl: Box::new(decl.unwrap()),
            cv,
        };

        (tok, ptr)
    }
}
