use crate::lexer::Token;
use bitflags::bitflags;

bitflags! {
    pub struct Specifier: u16 {
        const TYPEDEF = 0b1;
        const INLINE = 0b10;
        const FRIEND = 0b100;
        const CONSTEVAL = 0b1000;
        const CONSTEXPR = 0b1_0000;
        const CONSTINIT = 0b10_0000;
        const REGISTER = 0b100_0000;
        const STATIC = 0b1000_0000;
        const THREAD_LOCAL = 0b1_0000_0000;
        const EXTERN = 0b10_0000_0000;
        const MUTABLE = 0b100_0000_0000;
    }
}

impl Specifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Typedef => {
                *self |= Specifier::TYPEDEF;
                true
            }
            Token::Inline => {
                *self |= Specifier::INLINE;
                true
            }
            Token::Friend => {
                *self |= Specifier::FRIEND;
                true
            }
            Token::Consteval => {
                *self |= Specifier::CONSTEVAL;
                true
            }
            Token::Constexpr => {
                *self |= Specifier::CONSTEXPR;
                true
            }
            Token::Constinit => {
                *self |= Specifier::CONSTINIT;
                true
            }
            Token::Register => {
                *self |= Specifier::REGISTER;
                true
            }
            Token::Static => {
                *self |= Specifier::STATIC;
                true
            }
            Token::ThreadLocal => {
                *self |= Specifier::THREAD_LOCAL;
                true
            }
            Token::Extern => {
                *self |= Specifier::EXTERN;
                true
            }
            Token::Mutable => {
                *self |= Specifier::MUTABLE;
                true
            }
            _ => false,
        }
    }
}
