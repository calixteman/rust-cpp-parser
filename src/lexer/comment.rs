use super::lexer::{Lexer, Token};
use super::preprocessor::context::PreprocContext;

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    pub(crate) fn get_multiline_comment(&mut self) -> Token<'a> {
        self.buf.inc();
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'/' {
                    let c = self.buf.prev_char();
                    if c == b'*' {
                        let comment = self.buf.slice_m_n(spos, 1);
                        self.buf.inc();
                        return Token::Comment(comment);
                    }
                    self.buf.inc();
                } else if c == b'\n' {
                    self.buf.add_new_line();
                    self.buf.inc();
                } else {
                    self.buf.inc();
                }
            } else {
                break;
            }
        }

        let comment = self.buf.slice(spos);
        Token::Comment(comment)
    }

    pub(crate) fn get_single_comment(&mut self) -> Token<'a> {
        let spos = self.buf.pos() + 1;
        self.buf.inc();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                if c == b'\\' {
                    self.buf.inc();
                } else if c == b'\n' {
                    //self.buf.add_new_line();
                    let comment = self.buf.slice_m_n(spos, 1);
                    self.buf.dec();
                    return Token::Comment(comment);
                }
            } else {
                break;
            }
        }

        let comment = self.buf.slice(spos);
        Token::Comment(comment)
    }

    #[inline(always)]
    pub(crate) fn skip_multiline_comment(&mut self) {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'/' {
                    let c = self.buf.prev_char();
                    if c == b'*' {
                        self.buf.inc();
                        break;
                    }
                    self.buf.inc();
                } else if c == b'\n' {
                    self.buf.inc();
                    self.buf.add_new_line();
                } else {
                    self.buf.inc();
                }
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
                    self.buf.inc();
                } else {
                    self.buf.inc();
                }
            } else {
                break;
            }
        }
    }
}
