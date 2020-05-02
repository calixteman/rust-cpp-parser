// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

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

