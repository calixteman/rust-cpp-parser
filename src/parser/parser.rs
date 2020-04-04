use hashbrown::{hash_map, HashMap};

use super::lexer::{Lexer, Token};

struct Parser<'a> {
    buf: &'a [u8],
    lexer: Lexer<'a>,
    //types: HashMap<&'a str, 
}

impl<'a> Parser<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            lexer: Lexer::new(buf),
        }
    }
}

