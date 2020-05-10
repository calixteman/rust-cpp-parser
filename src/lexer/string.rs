// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::lexer::{Lexer, Token};
use super::preprocessor::context::PreprocContext;

#[derive(PartialEq)]
pub(crate) enum StringType {
    None,
    L,
    UU,
    R,
    U,
    U8,
    LR,
    UUR,
    UR,
    U8R,
}

pub(crate) enum StringCharType {
    S(StringType),
    C(StringType),
}

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    #[inline(always)]
    pub(crate) fn get_string_char_prefix(&mut self, typ: StringType) -> Option<StringCharType> {
        // L, U, LR, UR, u, uR, u8, u8R
        match self.buf.rem() {
            #[cold]
            0 | 1 => {
                return None;
            }
            #[cold]
            2 => {
                let c = self.buf.next_char();
                if c == b'\"' {
                    self.buf.inc();
                    return Some(StringCharType::S(typ));
                } else if c == b'\'' {
                    self.buf.inc();
                    return Some(StringCharType::C(typ));
                }
            }
            _ => {
                let c = self.buf.next_char();
                if c == b'\"' {
                    self.buf.inc();
                    return Some(StringCharType::S(typ));
                } else if c == b'\'' {
                    self.buf.inc();
                    return Some(StringCharType::C(typ));
                } else if c == b'R' {
                    let c = self.buf.next_char_n(1);
                    if c == b'\"' {
                        self.buf.inc_n(2);
                        return Some(StringCharType::S(match typ {
                            StringType::L => StringType::LR,
                            StringType::UU => StringType::UUR,
                            StringType::U => StringType::UR,
                            _ => unreachable!(),
                        }));
                    }
                } else if typ == StringType::U && c == b'8' {
                    let c = self.buf.next_char_n(1);
                    if c == b'\"' {
                        self.buf.inc_n(2);
                        return Some(StringCharType::S(StringType::U8));
                    } else if c == b'\'' {
                        self.buf.inc_n(2);
                        return Some(StringCharType::C(StringType::U8));
                    } else if c == b'R' {
                        let c = self.buf.next_char_n(2);
                        if c == b'\"' {
                            self.buf.inc_n(3);
                            return Some(StringCharType::S(StringType::U8R));
                        }
                    }
                }
            }
        }
        None
    }

    #[inline(always)]
    pub(crate) fn get_special_string_char(&mut self, typ: StringType) -> Option<Token> {
        if let Some(typ) = self.get_string_char_prefix(typ) {
            Some(match typ {
                StringCharType::S(typ) => self.get_string(typ),
                StringCharType::C(typ) => self.get_char(typ),
            })
        } else {
            None
        }
    }

    #[inline(always)]
    pub(super) fn get_string(&mut self, typ: StringType) -> Token {
        match typ {
            StringType::L => {
                let s = self.get_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralLStringUD(s)
                } else {
                    Token::LiteralLString(s)
                }
            }
            StringType::UU => {
                let s = self.get_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralUUStringUD(s)
                } else {
                    Token::LiteralUUString(s)
                }
            }
            StringType::R => {
                let s = self.get_r_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralRStringUD(s)
                } else {
                    Token::LiteralRString(s)
                }
            }
            StringType::U => {
                let s = self.get_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralUStringUD(s)
                } else {
                    Token::LiteralUString(s)
                }
            }
            StringType::U8 => {
                let s = self.get_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralU8StringUD(s)
                } else {
                    Token::LiteralU8String(s)
                }
            }
            StringType::LR => {
                let s = self.get_r_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralLRStringUD(s)
                } else {
                    Token::LiteralLRString(s)
                }
            }
            StringType::UUR => {
                let s = self.get_r_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralUURStringUD(s)
                } else {
                    Token::LiteralUURString(s)
                }
            }
            StringType::UR => {
                let s = self.get_r_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralURStringUD(s)
                } else {
                    Token::LiteralURString(s)
                }
            }
            StringType::U8R => {
                let s = self.get_r_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralU8RStringUD(s)
                } else {
                    Token::LiteralU8RString(s)
                }
            }
            StringType::None => {
                let s = self.get_string_content();
                if let Some(suf) = self.get_suffix() {
                    let s = Box::new((s, suf));
                    Token::LiteralStringUD(s)
                } else {
                    Token::LiteralString(s)
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_string_content(&mut self) -> String {
        let mut buf = Vec::new();
        let mut spos = self.buf.pos();
        let mut ch = String::new();

        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b'\\' {
                    let pos = self.buf.pos();
                    self.buf.inc();
                    if let Some(code) = self.get_escape() {
                        buf.extend_from_slice(self.buf.slice_p(spos, pos));
                        ch.push(std::char::from_u32(code).unwrap());
                        buf.extend_from_slice(ch.as_bytes());
                        ch.clear();
                        spos = self.buf.pos();
                    }
                } else if c == b'\"' {
                    let s = if buf.is_empty() {
                        String::from_utf8(self.buf.slice(spos).to_vec()).unwrap()
                    } else {
                        buf.extend_from_slice(self.buf.slice(spos));
                        String::from_utf8(buf).unwrap()
                    };
                    self.buf.inc();
                    return s;
                } else {
                    self.buf.inc();
                }
            } else {
                return if buf.is_empty() {
                    String::from_utf8(self.buf.slice(spos).to_vec()).unwrap()
                } else {
                    buf.extend_from_slice(self.buf.slice(spos));
                    String::from_utf8(buf).unwrap()
                };
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_r_string_content(&mut self) -> String {
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                if c == b'(' {
                    break;
                }
            } else {
                return String::from_utf8(self.buf.slice(spos).to_vec()).unwrap();
            }
        }

        // delimiter doesn't contain parenthesis, spaces or backslashes
        let delimiter = self.buf.slice_m_n(spos, 1);
        let delim_len = delimiter.len();

        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == b')' {
                    let rspos = self.buf.pos();
                    let mut delim_pos = 0;
                    self.buf.inc();
                    loop {
                        let c = self.buf.next_char();

                        if delim_pos < delim_len {
                            let d = unsafe { *delimiter.get_unchecked(delim_pos) };

                            if c != d {
                                break;
                            }

                            self.buf.inc();
                            delim_pos += 1;
                        } else if c == b'\"' {
                            self.buf.inc();
                            return String::from_utf8(self.buf.slice_p(spos, rspos).to_vec())
                                .unwrap();
                        } else if c == b'\n' {
                            self.buf.add_new_line();
                            self.buf.inc();
                            break;
                        } else {
                            break;
                        }
                    }
                } else if c == b'\n' {
                    self.buf.add_new_line();
                    self.buf.inc();
                } else {
                    self.buf.inc();
                }
            } else {
                return String::from_utf8(self.buf.slice(spos).to_vec()).unwrap();
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_by_delim(&mut self, delim: u8) {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == delim {
                    self.buf.inc();
                    break;
                } else if c == b'\\' {
                    self.buf.inc();
                    if self.buf.has_char() {
                        let c = self.buf.next_char();
                        if c == b'\n' {
                            self.buf.add_new_line();
                        }
                        self.buf.inc();
                    } else {
                        break;
                    }
                } else {
                    self.buf.inc();
                }
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
    fn test_string() {
        let mut p = Lexer::<DefaultContext>::new(b"\"foo\" \"foo\\\"bar\"");
        assert_eq!(p.next_token(), Token::LiteralString("foo".to_string()));
        assert_eq!(p.next_token(), Token::LiteralString("foo\"bar".to_string()));

        let mut p = Lexer::<DefaultContext>::new(b"u\"foo\" u\"foo\\\"bar\"");
        assert_eq!(p.next_token(), Token::LiteralUString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralUString("foo\"bar".to_string())
        );

        let mut p = Lexer::<DefaultContext>::new(b"U\"foo\" U\"foo\\\"bar\"");
        assert_eq!(p.next_token(), Token::LiteralUUString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralUUString("foo\"bar".to_string())
        );

        let mut p = Lexer::<DefaultContext>::new(b"u8\"foo\" u8\"foo\\\"bar\"");
        assert_eq!(p.next_token(), Token::LiteralU8String("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralU8String("foo\"bar".to_string())
        );

        let mut p = Lexer::<DefaultContext>::new(b"L\"foo\" L\"foo\\\"bar\"");
        assert_eq!(p.next_token(), Token::LiteralLString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralLString("foo\"bar".to_string())
        );

        let mut p = Lexer::<DefaultContext>::new(
            b"R\"hello(foo)hello\" R\"world(foo\n\\\"bar)world\" R\"world(foo)world  )world\"",
        );
        assert_eq!(p.next_token(), Token::LiteralRString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralRString("foo\n\\\"bar".to_string())
        );
        assert_eq!(
            p.next_token(),
            Token::LiteralRString("foo)world  ".to_string())
        );

        let mut p =
            Lexer::<DefaultContext>::new(b"LR\"hello(foo)hello\" UR\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next_token(), Token::LiteralLRString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralUURString("foo\n\\\"bar".to_string())
        );

        let mut p =
            Lexer::<DefaultContext>::new(b"uR\"hello(foo)hello\" u8R\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next_token(), Token::LiteralURString("foo".to_string()));
        assert_eq!(
            p.next_token(),
            Token::LiteralU8RString("foo\n\\\"bar".to_string())
        );

        let mut p = Lexer::<DefaultContext>::new(b"R\"(abc)\ndef)\n)\"");
        assert_eq!(
            p.next_token(),
            Token::LiteralRString("abc)\ndef)\n".to_string())
        );

        let mut p =
            Lexer::<DefaultContext>::new(b"\"test\\0\\\\\\\"\\t\\a\\b\\234\\u1234\\U0010ffff\"");
        assert_eq!(
            p.next_token(),
            Token::LiteralString("test\u{0}\\\"\t\u{7}\u{8}\u{9c}\u{1234}\u{10ffff}".to_string())
        );
    }

    #[test]
    fn test_string_suffix() {
        let mut p = Lexer::<DefaultContext>::new(b"\"foo\"_abcde");
        assert_eq!(
            p.next_token(),
            Token::LiteralStringUD(Box::new(("foo".to_string(), "_abcde".to_string())))
        );
    }
}
