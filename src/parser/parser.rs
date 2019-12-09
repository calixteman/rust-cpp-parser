use super::lexer::{Lexer, Token};

struct Parser<'a> {
    buf: &'a [u8],
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            lexer: Lexer::new(buf),
        }
    }
}

