use crate::lexer::Token;
use bitflags::bitflags;

bitflags! {
    pub(crate) struct Modifier: u64 {
        const SIGNED = 0b1;
        const UNSIGNED = 0b10;
        const CHAR = 0b100;
        const SHORT = 0b1000;
        const INT = 0b1_0000;
        const LONG = 0b10_0000;
        const LONGLONG = 0b100_0000;
        const FLOAT = 0b1000_0000;
        const DOUBLE = 0b1_0000_0000;
        const BOOL = 0b10_0000_0000;
        const WCHART = 0b100_0000_0000;
        const CHAR8T = 0b1000_0000_0000;
        const CHAR16T = 0b1_0000_0000_0000;
        const CHAR32T = 0b10_0000_0000_0000;
        const COMPLEX = 0b100_0000_0000_0000;
        const IMAGINARY = 0b1000_0000_0000_0000;
        const VOID = 0b1_0000_0000_0000_0000;
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Primitive {
    Void,
    Char,
    SignedChar,
    Short,
    Int,
    Long,
    LongLong,
    UnsignedChar,
    UnsignedShort,
    UnsignedInt,
    UnsignedLong,
    UnsignedLongLong,
    Float,
    Double,
    LongDouble,
    FloatComplex,
    DoubleComplex,
    LongDoubleComplex,
    FloatImaginary,
    DoubleImaginary,
    LongDoubleImaginary,
    Bool,
    WcharT,
    Char8T,
    Char16T,
    Char32T,
}

impl Modifier {
    pub(crate) fn to_primitive(self) -> Primitive {
        match self.bits() {
            0b100 => Primitive::Char,
            0b101 => Primitive::SignedChar,
            0b110 => Primitive::UnsignedChar,
            0b1001 | 0b1_1001 | 0b1_1000 | 0b1000 => Primitive::Short,
            0b1010 | 0b1_1010 => Primitive::UnsignedShort,
            0b1_0000 | 0b1_0001 | 0b1 => Primitive::Int,
            0b1_0010 | 0b10 => Primitive::UnsignedInt,
            0b10_0000 | 0b11_0000 | 0b10_0001 | 0b11_0001 => Primitive::Long,
            0b10_0010 | 0b11_0010 => Primitive::UnsignedLong,
            0b100_0000 | 0b101_0000 | 0b100_0001 | 0b101_0001 => Primitive::LongLong,
            0b100_0010 | 0b101_0010 => Primitive::UnsignedLongLong,
            0b1000_0000 => Primitive::Float,
            0b1_0000_0000 => Primitive::Double,
            0b1_0010_0000 => Primitive::LongDouble,
            0b10_0000_0000 => Primitive::Bool,
            0b100_0000_0000 => Primitive::WcharT,
            0b1000_0000_0000 => Primitive::Char8T,
            0b1_0000_0000_0000 => Primitive::Char16T,
            0b10_0000_0000_0000 => Primitive::Char32T,
            0b100_0000_1000_0000 => Primitive::FloatComplex,
            0b100_0001_0000_0000 => Primitive::DoubleComplex,
            0b100_0001_0010_0000 => Primitive::LongDoubleComplex,
            0b1000_0000_1000_0000 => Primitive::FloatImaginary,
            0b1000_0001_0000_0000 => Primitive::DoubleImaginary,
            0b1000_0001_0010_0000 => Primitive::LongDoubleImaginary,
            0b1_0000_0000_0000_0000 => Primitive::Void,
            _ => unreachable!("Invalid modifier {:?}", self),
        }
    }

    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Signed => {
                *self |= Modifier::SIGNED;
                true
            }
            Token::Unsigned => {
                *self |= Modifier::UNSIGNED;
                true
            }
            Token::Char => {
                *self |= Modifier::CHAR;
                true
            }
            Token::Short => {
                *self |= Modifier::SHORT;
                true
            }
            Token::Int => {
                *self |= Modifier::INT;
                true
            }
            Token::Long => {
                if self.intersects(Modifier::LONG) {
                    self.remove(Modifier::LONG);
                    *self |= Modifier::LONGLONG;
                } else {
                    *self |= Modifier::LONG;
                }
                true
            }
            Token::Float => {
                *self |= Modifier::FLOAT;
                true
            }
            Token::Double => {
                *self |= Modifier::DOUBLE;
                true
            }
            Token::Complex => {
                *self |= Modifier::COMPLEX;
                true
            }
            Token::Imaginary => {
                *self |= Modifier::IMAGINARY;
                true
            }
            Token::Bool => {
                *self |= Modifier::BOOL;
                true
            }
            Token::WcharT => {
                *self |= Modifier::WCHART;
                true
            }
            Token::Char8T => {
                *self |= Modifier::CHAR8T;
                true
            }
            Token::Char16T => {
                *self |= Modifier::CHAR16T;
                true
            }
            Token::Char32T => {
                *self |= Modifier::CHAR32T;
                true
            }
            Token::Void => {
                *self |= Modifier::VOID;
                true
            }
            _ => false,
        }
    }
}
