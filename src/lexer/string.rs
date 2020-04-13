use super::lexer::{Lexer, Token};
use super::preprocessor::context::PreprocContext;

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum StringType {
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

#[derive(Clone, Copy, Debug, PartialEq)]
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
    pub(crate) fn get_special_string_char(&mut self, typ: StringType) -> Option<Token<'a>> {
        if let Some(typ) = self.get_string_char_prefix(typ) {
            Some(match typ {
                StringCharType::S(typ) => match typ {
                    StringType::L => Token::LiteralLString(self.get_string_content()),
                    StringType::UU => Token::LiteralUUString(self.get_string_content()),
                    StringType::R => Token::LiteralRString(self.get_r_string_content()),
                    StringType::U => Token::LiteralUString(self.get_string_content()),
                    StringType::U8 => Token::LiteralU8String(self.get_string_content()),
                    StringType::LR => Token::LiteralLRString(self.get_r_string_content()),
                    StringType::UUR => Token::LiteralUURString(self.get_r_string_content()),
                    StringType::UR => Token::LiteralURString(self.get_r_string_content()),
                    StringType::U8R => Token::LiteralU8RString(self.get_r_string_content()),
                },
                StringCharType::C(typ) => match typ {
                    StringType::L => Token::LiteralLChar(self.get_c_char_u32()),
                    StringType::UU => Token::LiteralUUChar(self.get_c_char_u32()),
                    StringType::U => Token::LiteralUChar(self.get_c_char_u32()),
                    StringType::U8 => Token::LiteralU8Char(self.get_c_char_u32()),
                    _ => unreachable!(),
                },
            })
        } else {
            None
        }
    }

    #[inline(always)]
    pub(crate) fn get_string(&mut self) -> Token<'a> {
        Token::LiteralString(self.get_string_content())
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
