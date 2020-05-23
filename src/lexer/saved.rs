// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{TLexer, Token};

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SavedLexer {
    toks: Vec<Token>,
    pos: usize,
}

impl TLexer for SavedLexer {
    fn next_useful(&mut self) -> Token {
        if let Some(tok) = self.toks.get(self.pos) {
            self.pos += 1;
            tok.clone()
        } else {
            Token::Eof
        }
    }
}

impl SavedLexer {
    pub(crate) fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer, Token};
    use pretty_assertions::assert_eq;

    #[test]
    fn test_saved_lexer() {
        let mut l = Lexer::<DefaultContext>::new(b"(1 + 2 * 3) + (4 - 5))");
        let (_, saved) = l.save_until(Token::RightParen);

        assert_eq!(
            saved.toks,
            vec![
                Token::LeftParen,
                Token::LiteralInt(1),
                Token::Plus,
                Token::LiteralInt(2),
                Token::Star,
                Token::LiteralInt(3),
                Token::RightParen,
                Token::Plus,
                Token::LeftParen,
                Token::LiteralInt(4),
                Token::Minus,
                Token::LiteralInt(5),
                Token::RightParen
            ]
        );
    }
}
