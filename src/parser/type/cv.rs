use crate::lexer::Token;
use bitflags::bitflags;

bitflags! {
    pub(crate) struct CVQualifier: u8 {
        const CONST = 0b1;
        const VOLATILE = 0b10;
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
            _ => false,
        }
    }
}
