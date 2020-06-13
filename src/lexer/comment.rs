// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::lexer::{Lexer, Token};
use super::preprocessor::context::PreprocContext;

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    pub(crate) fn get_multiline_comment(&mut self) -> Token {
        self.buf.inc();
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'/' {
                    // TODO: we can have a continuation line between '*' and '/'
                    let c = self.buf.prev_char();
                    if c == b'*' && self.buf.pos() != spos {
                        let comment = self.buf.slice_m_n(spos, 1);
                        self.buf.inc();
                        self.comment = Some(comment);
                        return Token::Comment;
                    }
                } else if c == b'\n' {
                    self.buf.add_new_line();
                }
                self.buf.inc();
            } else {
                break;
            }
        }

        let comment = self.buf.slice(spos);
        self.comment = Some(comment);
        Token::Comment
    }

    pub(crate) fn get_single_comment(&mut self) -> Token {
        let spos = self.buf.pos() + 1;
        self.buf.inc();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                if c == b'\\' {
                    self.buf.inc();
                    if self.buf.has_char() {
                        let c = self.buf.next_char();
                        if c == b'\n' {
                            self.buf.add_new_line();
                        }
                    }
                } else if c == b'\n' {
                    //self.buf.add_new_line();
                    let comment = self.buf.slice_m_n(spos, 1);
                    self.buf.dec();
                    self.comment = Some(comment);
                    return Token::Comment;
                }
            } else {
                break;
            }
        }

        let comment = self.buf.slice(spos);
        self.comment = Some(comment);
        Token::Comment
    }

    #[inline(always)]
    pub(crate) fn skip_multiline_comment(&mut self) {
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'/' {
                    let c = self.buf.prev_char();
                    if c == b'*' && self.buf.pos() != spos {
                        self.buf.inc();
                        break;
                    }
                } else if c == b'\n' {
                    self.buf.add_new_line();
                }
                self.buf.inc();
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_single_comment(&mut self) {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'\n' {
                    // no buf.add_new_line here (will be done later)
                    break;
                } else if c == b'\\' {
                    self.buf.inc();
                    if self.buf.has_char() {
                        let c = self.buf.next_char();
                        if c == b'\n' {
                            self.buf.add_new_line();
                        }
                    }
                }
                self.buf.inc();
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_comment_1() {
        let mut p = Lexer::<DefaultContext>::new(b"/* test */");
        assert_eq!(p.next_token(), Token::Comment);
        assert_eq!(p.get_comment().unwrap(), b" test ");
    }

    #[test]
    fn test_comment_2() {
        let mut p = Lexer::<DefaultContext>::new(b"// one line comment \n");
        assert_eq!(p.next_token(), Token::Comment);
        assert_eq!(p.get_comment().unwrap(), b" one line comment ");
    }

    #[test]
    fn test_comment_3() {
        let mut p = Lexer::<DefaultContext>::new(b"/*/ */");
        assert_eq!(p.next_token(), Token::Comment);
        assert_eq!(p.get_comment().unwrap(), b"/ ");
    }
}
