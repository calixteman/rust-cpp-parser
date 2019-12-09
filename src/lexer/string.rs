use super::lexer::{Lexer, Token};

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

impl<'a> Lexer<'a> {
    #[inline(always)]
    pub(crate) fn get_string_char_prefix(&mut self, typ: StringType) -> Option<StringCharType> {
        // L, U, LR, UR, u, uR, u8, u8R
        let rem = self.len - self.pos;
        match rem {
            #[cold] 0 | 1 => {
                return None;
            }
            #[cold] 2 => {
                let c = self.next_char(0);
                if c == b'\"' {
                    self.pos += 1;
                    return Some(StringCharType::S(typ));
                } else if c == b'\'' {
                    self.pos += 1;
                    return Some(StringCharType::C(typ));
                }
            }
            _ => {
                let c = self.next_char(0);
                if c == b'\"' {
                    self.pos += 1;
                    return Some(StringCharType::S(typ));
                } else if c == b'\'' {
                    self.pos += 1;
                    return Some(StringCharType::C(typ));
                } else if c == b'R' {
                    let c = self.next_char(1);
                    if c == b'\"' {
                        self.pos += 2;
                        return Some(StringCharType::S(match typ {
                            StringType::L => StringType::LR,
                            StringType::UU => StringType::UUR,
                            StringType::U => StringType::UR,
                            _ => unreachable!(),
                        }));
                    }
                } else if typ == StringType::U && c == b'8' {
                    let c = self.next_char(1);
                    if c == b'\"' {
                        self.pos += 2;
                        return Some(StringCharType::S(StringType::U8));
                    } else if c == b'\'' {
                        self.pos += 2;
                        return Some(StringCharType::C(StringType::U8));
                    } else if c == b'R' {
                        let c = self.next_char(2);
                        if c == b'\"' {
                            self.pos += 3;
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
        return Token::LiteralString(self.get_string_content());
    }

    #[inline(always)]
    pub(crate) fn get_string_content(&mut self) -> &'a [u8] {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == b'\\' {
                    self.pos += 2;
                } else if c == b'\"' {
                    let s = unsafe { &self.buf.get_unchecked(spos..self.pos) };
                    self.pos += 1;
                    return s;
                } else {
                    self.pos += 1;
                }
            } else {
                return unsafe { &self.buf.get_unchecked(spos..) };
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_r_string_content(&mut self) -> &'a [u8] {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                self.pos += 1;
                if c == b'(' {
                    break;
                }
            } else {
                return unsafe { &self.buf.get_unchecked(spos..) };
            }
        }

        // delimiter doesn't contain parenthesis, spaces or backslashes
        let delimiter = unsafe { &self.buf.get_unchecked(spos..self.pos - 1) };
        let delim_len = delimiter.len();

        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == b')' {
                    let rspos = self.pos;
                    let mut delim_pos = 0;
                    self.pos += 1;
                    loop {
                        let c = self.next_char(0);

                        if delim_pos < delim_len {
                            let d = unsafe { *delimiter.get_unchecked(delim_pos) };

                            if c != d {
                                break;
                            }

                            self.pos += 1;
                            delim_pos += 1;
                        } else if c == b'\"' {
                            self.pos += 1;
                            return unsafe { &self.buf.get_unchecked(spos..rspos) };
                        } else if c == b'\n' {
                            self.add_new_line();
                        } else {
                            break;
                        }
                    }
                } else if c == b'\n' {
                    self.add_new_line();
                    self.pos += 1;
                } else {
                    self.pos += 1;
                }
            } else {
                return unsafe { &self.buf.get_unchecked(spos..) };
            }
        }
    }
}
