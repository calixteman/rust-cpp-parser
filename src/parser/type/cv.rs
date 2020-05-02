use crate::lexer::Token;
use bitflags::bitflags;

bitflags! {
    pub struct CVQualifier: u8 {
        const CONST = 0b1;
        const VOLATILE = 0b10;
        const RESTRICT = 0b100;
    }
}

impl CVQualifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Const => {
                *self |= CVQualifier::CONST;
                true
            }
            Token::Volatile => {
                *self |= CVQualifier::VOLATILE;
                true
            }
            Token::Restrict => {
                *self |= CVQualifier::RESTRICT;
                true
            }
            _ => false,
        }
    }

    pub(crate) fn is_cv(tok: &Token) -> bool {
        match tok {
            Token::Const | Token::Volatile | Token::Restrict => true,
            _ => false,
        }
    }
}
