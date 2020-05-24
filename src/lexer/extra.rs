// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::errors::Span;
use crate::lexer::{TLexer, Token};

#[derive(Clone, Debug)]
pub struct SavedLexer {
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

    fn span(&self) -> Span {
        Span::default()
    }
}

impl SavedLexer {
    pub fn new(toks: Vec<Token>) -> Self {
        Self { toks, pos: 0 }
    }

    pub fn push(&mut self, tok: Token) {
        self.toks.push(tok);
    }
}

pub struct CombinedLexers<'l1, 'l2> {
    first: &'l1 mut dyn TLexer,
    second: &'l2 mut dyn TLexer,
    state: bool,
}

impl<'l1, 'l2> TLexer for CombinedLexers<'l1, 'l2> {
    fn next_useful(&mut self) -> Token {
        let tok = if self.state {
            let tok = self.first.next_useful();
            if tok == Token::Eof {
                self.state = false;
                self.second.next_useful()
            } else {
                tok
            }
        } else {
            self.second.next_useful()
        };
        eprintln!("TOK: {:?}", tok);
        tok
    }

    fn span(&self) -> Span {
        if self.state {
            Span::default()
        } else {
            self.second.span()
        }
    }
}

impl<'l1, 'l2> CombinedLexers<'l1, 'l2> {
    pub fn new(first: &'l1 mut dyn TLexer, second: &'l2 mut dyn TLexer) -> Self {
        Self {
            first,
            second,
            state: true,
        }
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
                Token::RightParen,
                Token::RightParen
            ]
        );
    }
}
