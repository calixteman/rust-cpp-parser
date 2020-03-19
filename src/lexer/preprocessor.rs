use bitflags::bitflags;
use hashbrown::HashMap;

use super::condition::Condition;
use super::lexer::{Lexer, Token};
use super::macro_args::MacroDefArg;
use super::pmacros::{
    Action, IfKind, IfState, Macro, MacroFunction, MacroObject, MacroType, PContext,
};
use super::string::StringType;

#[derive(Clone, Debug, Copy, PartialEq, PartialOrd)]
#[repr(u8)]
pub(crate) enum Kind {
    IDE = 0, // usual id parts
    IDL = 1, // L, R, U, u for string starter
    IDR = 2,
    IDU = 3,
    IDu = 4,
    NUM = 5,  // 0-9
    SPA = 6,  // space
    HAS = 7,  // hash
    QUO = 8,  // " or '
    RET = 9,  // return
    SLA = 10, // slash
    BAC = 11, // backslash
    NON = 12, // nothing
}

#[rustfmt::skip]
pub(crate) const PPCHARS: [Kind; 256] = [
    // 0 NUL   1 SOH      2 STX      3 ETX      4 EOT      5 ENQ      6 ACK      7 BEL
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 8 BS    9 HT       A NL       B VT       C NP       D CR       E SO       F SI
    Kind::NON, Kind::SPA, Kind::RET, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 10 DLE  11 DC1     12 DC2     13 DC3     14 DC4     15 NAK     16 SYN     17 ETB
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 18 CAN  19 EM      1A SUB     1B ESC     1C FS      1D GS      1E RS      1F US
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 20 SP   21  !      22  "      23  #      24  $      25  %      26  &      27  '
    Kind::SPA, Kind::NON, Kind::QUO, Kind::HAS, Kind::NON, Kind::NON, Kind::NON, Kind::QUO, //
    // 28  (   29  )      2A  *      2B  +      2C  ,      2D  -      2E  .      2F   /
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::SLA, //
    // 30  0   31  1      32  2      33  3      34  4      35  5      36  6      37  7
    Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, //
    // 38  8   39  9      3A  :      3B  ;      3C  <      3D  =      3E  >      3F  ?
    Kind::NUM, Kind::NUM, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 40  @   41  A      42  B      43  C      44  D      45  E      46  F      47  G
    Kind::NON, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 48  H   49  I      4A  J      4B  K      4C  L      4D  M      4E  N      4F  O
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDL, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 50  P   51  Q      52  R      53  S      54  T      55  U      56  V      57  W
    Kind::IDE, Kind::IDE, Kind::IDR, Kind::IDE, Kind::IDE, Kind::IDU, Kind::IDE, Kind::IDE, //
    // 58  X   59  Y      5A  Z      5B  [      5C  \      5D  ]      5E  ^      5F  _
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::NON, Kind::BAC, Kind::NON, Kind::IDE, Kind::IDE, //
    // 60  `   61  a      62  b      63  c      64  d      65  e      66  f      67  g
    Kind::NON, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 68  h   69  i      6A  j      6B  k      6C  l      6D  m      6E  n      6F  o
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 70  p   71  q      72  r      73  s      74  t      75  u      76  v      77  w
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDu, Kind::IDE, Kind::IDE, //
    // 78  x   79  y      7A  z      7B  {      7C  |      7D  }      7E  ~      7F DEL
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, // 
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
];

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IncludeType<'a> {
    Quote(&'a [u8]),
    Angle(&'a [u8]),
    Other(&'a [u8]),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LastKind {
    None,
    Arg(usize),
    Concat,
    Id,
    Space,
}

#[derive(Clone, Debug, PartialEq)]
pub enum MacroToken<'a> {
    None(&'a [u8]),
    Id(&'a str),
    Space,
    Stringify,
    WhiteStringify,
    Concat,
    Eom,
}

impl<'a> Lexer<'a> {
    #[inline(always)]
    pub fn preproc_parse(&mut self, instr: Token<'a>) -> Token<'a> {
        // https://docs.freebsd.org/info/cpp/cpp.pdf
        skip_whites!(self);
        match instr {
            Token::PreprocInclude2 => Token::PreprocInclude(self.get_include()),
            Token::PreprocIncludeNext2 => Token::PreprocIncludeNext(self.get_include()),
            Token::PreprocUndef => {
                self.get_undef();
                Token::PreprocUndef
            }
            Token::PreprocIf => {
                if !self.get_if(IfKind::If) {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocIfdef => {
                if !self.get_if(IfKind::Ifdef) {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocIfndef => {
                if !self.get_if(IfKind::Ifndef) {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocElif => {
                if !self.get_elif() {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocElse => {
                if !self.get_else() {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocEndif => {
                if !self.get_endif() {
                    self.skip_until_else_endif();
                }
                Token::None
            }
            Token::PreprocDefine => {
                self.get_define();
                Token::None
            }
            _ => instr,
        }
    }

    #[inline(always)]
    pub(crate) fn get_preproc_identifier(&mut self) -> &'a str {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *PPCHARS.get_unchecked(c as usize) };
                if kind > Kind::NUM {
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }

        unsafe { std::str::from_utf8_unchecked(&self.buf.get_unchecked(spos..self.pos)) }
    }

    #[inline(always)]
    pub(crate) fn get_include_content(&mut self, term: u8) -> &'a [u8] {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == term {
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
    pub(crate) fn get_include(&mut self) -> IncludeType<'a> {
        skip_whites!(self);
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'\"' {
                self.pos += 1;
                return IncludeType::Quote(self.get_include_content(b'\"'));
            } else if c == b'<' {
                self.pos += 1;
                return IncludeType::Angle(self.get_include_content(b'>'));
            } else {
                let spos = self.pos;
                skip_until!(self, b'\n');
                self.add_new_line();
                let code = unsafe { self.buf.get_unchecked(spos..self.pos) };
                self.pos += 1;
                return IncludeType::Other(code);
            }
        }
        IncludeType::Other(&[])
    }

    #[inline(always)]
    pub(crate) fn get_macro_arguments(&mut self) -> (HashMap<&'a str, usize>, Option<usize>) {
        let mut args = HashMap::default();
        let mut n = 0;
        let mut va_args = None;
        skip_whites!(self);
        let c = self.next_char(0);
        if c == b')' {
            return (args, va_args);
        }

        loop {
            let arg = self.get_define_argument();
            match arg {
                MacroDefArg::Normal(id) => {
                    args.insert(id, n);
                }
                MacroDefArg::VaArgs => {
                    va_args = Some(n);
                    args.insert("__VA_ARGS__", n);
                }
                MacroDefArg::NamedVaArgs(va) => {
                    va_args = Some(n);
                    args.insert(va, n);
                }
            }
            skip_whites!(self);
            let c = self.next_char(0);
            self.pos += 1;
            skip_whites!(self);
            if c == b')' {
                break;
            }
            n += 1;
        }
        (args, va_args)
    }

    #[inline(always)]
    pub(crate) fn skip_multiline_comment(&mut self) {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == b'/' {
                    let c = self.prev_char(1);
                    if c == b'*' {
                        self.pos += 1;
                        break;
                    }
                    self.pos += 1;
                } else if c == b'\n' {
                    self.pos += 1;
                    self.add_new_line();
                } else {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_single_comment(&mut self) {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == b'\n' {
                    // no add_new_line here (will be done later)
                    break;
                } else if c == b'\\' {
                    self.pos += 2;
                } else {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_by_delim(&mut self, delim: u8) {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == delim {
                    self.pos += 1;
                    break;
                } else if c == b'\\' {
                    self.pos += 1;
                    if self.pos < self.len {
                        let c = self.next_char(0);
                        if c == b'\n' {
                            self.add_new_line();
                        }
                        self.pos += 1;
                    } else {
                        break;
                    }
                } else {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_slash_or_not(&mut self) -> bool {
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'/' {
                self.pos += 1;
                self.skip_single_comment();
                false
            } else if c == b'*' {
                self.pos += 1;
                self.skip_multiline_comment();
                false
            } else {
                true
            }
        } else {
            true
        }
    }

    #[inline(always)]
    pub(crate) fn rm_white(out: &mut Vec<u8>) {
        if let Some(last) = out.last() {
            if *last == b' ' {
                out.pop();
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_none(&mut self) {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *PPCHARS.get_unchecked(c as usize) };
                if kind != Kind::NON {
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_spaces_or_hash(&mut self) -> MacroToken<'a> {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *PPCHARS.get_unchecked(c as usize) };
                if kind != Kind::SPA {
                    if c != b'#' {
                        return MacroToken::Space;
                    }

                    self.pos += 1;
                    if self.pos < self.len {
                        let c = self.next_char(0);
                        if c == b'#' {
                            self.pos += 1;
                            skip_whites!(self);
                            return MacroToken::Concat;
                        }
                        return MacroToken::WhiteStringify;
                    }
                }
                self.pos += 1;
            } else {
                break;
            }
        }
        MacroToken::Space
    }

    #[inline(always)]
    pub(crate) fn next_macro_token(&mut self) -> MacroToken<'a> {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *PPCHARS.get_unchecked(c as usize) };
                match kind {
                    Kind::IDE => {
                        return MacroToken::Id(self.get_preproc_identifier());
                    }
                    Kind::IDL => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::L).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroToken::None(s);
                        } else {
                            self.pos -= 1;
                            return MacroToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDR => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::R).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroToken::None(s);
                        } else {
                            self.pos -= 1;
                            return MacroToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDU => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::UU).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroToken::None(s);
                        } else {
                            self.pos -= 1;
                            return MacroToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDu => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::U).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroToken::None(s);
                        } else {
                            self.pos -= 1;
                            return MacroToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::NUM => {
                        let p = self.pos;
                        self.pos += 1;
                        self.skip_number(c);
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroToken::None(s);
                    }
                    Kind::SPA => {
                        self.pos += 1;
                        return self.skip_spaces_or_hash();
                    }
                    Kind::HAS => {
                        self.pos += 1;
                        if self.pos < self.len {
                            let c = self.next_char(0);
                            if c == b'#' {
                                self.pos += 1;
                                skip_whites!(self);
                                return MacroToken::Concat;
                            }
                            return MacroToken::Stringify;
                        }
                    }
                    Kind::QUO => {
                        // we've a string or char literal
                        let p = self.pos;
                        self.pos += 1;
                        self.skip_by_delim(c);
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroToken::None(s);
                    }
                    Kind::RET => {
                        self.pos += 1;
                        self.add_new_line();
                        break;
                    }
                    Kind::SLA => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.skip_slash_or_not() {
                            let s = unsafe { self.buf.get_unchecked(p..p + 1) };
                            return MacroToken::None(s);
                        }
                    }
                    Kind::BAC => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.pos < self.len {
                            let c = self.next_char(0);
                            if c == b'\n' {
                                self.add_new_line();
                                self.pos += 1;
                            } else {
                                let s = unsafe { self.buf.get_unchecked(p..p + 1) };
                                return MacroToken::None(s);
                            }
                        } else {
                            let s = unsafe { self.buf.get_unchecked(p..p + 1) };
                            return MacroToken::None(s);
                        }
                    }
                    Kind::NON => {
                        let p = self.pos;
                        self.skip_none();
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroToken::None(s);
                    }
                }
            } else {
                break;
            }
        }
        MacroToken::Eom
    }

    #[inline(always)]
    pub(crate) fn get_function_definition(
        &mut self,
        args: HashMap<&str, usize>,
        va_args: Option<usize>,
    ) -> MacroFunction {
        let mut out = Vec::with_capacity(1024);
        let mut actions = Vec::with_capacity(args.len());
        let mut last_kind = LastKind::None;
        let mut last_chunk_end = 0;

        loop {
            let tok = self.next_macro_token();
            match tok {
                MacroToken::None(s) => {
                    out.extend_from_slice(s);
                    last_kind = LastKind::None;
                }
                MacroToken::Id(id) => {
                    if let Some(arg_pos) = args.get(id) {
                        let n = *arg_pos;
                        if last_chunk_end != out.len() {
                            actions.push(Action::Chunk(out.len()));
                            last_chunk_end = out.len();
                        }
                        match last_kind {
                            LastKind::Concat => {
                                actions.push(Action::Concat(n));
                            }
                            _ => {
                                actions.push(Action::Arg(n));
                            }
                        }
                        last_kind = LastKind::Arg(n);
                    } else {
                        out.extend_from_slice(id.as_bytes());
                        last_kind = LastKind::None;
                    }
                }
                MacroToken::Space => {
                    if last_kind != LastKind::Space {
                        out.push(b' ');
                        last_kind = LastKind::Space;
                    }
                }
                MacroToken::WhiteStringify | MacroToken::Stringify => {
                    if tok == MacroToken::WhiteStringify {
                        if last_kind != LastKind::Space {
                            out.push(b' ');
                            last_kind = LastKind::Space;
                        }
                    }
                    let id = self.get_preproc_identifier();
                    if let Some(arg_pos) = args.get(id) {
                        out.extend_from_slice(b"\"\"");
                        if last_chunk_end != out.len() - 1 {
                            actions.push(Action::Chunk(out.len() - 1));
                            last_chunk_end = out.len() - 1;
                        }
                        actions.push(Action::Stringify(*arg_pos));
                    } else {
                        out.push(b'#');
                        out.extend_from_slice(id.as_bytes());
                    }
                    last_kind = LastKind::None;
                }
                MacroToken::Concat => {
                    match last_kind {
                        LastKind::Arg(n) => {
                            actions.pop();
                            actions.push(Action::Concat(n));
                        }
                        _ => {}
                    }
                    last_kind = LastKind::Concat;
                }
                MacroToken::Eom => {
                    break;
                }
            }
        }

        MacroFunction::new(out, actions, args.len(), va_args)
    }

    #[inline(always)]
    pub(crate) fn get_object_definition(&mut self) -> MacroObject {
        let mut out = Vec::with_capacity(64);
        let mut last_kind = LastKind::None;
        let mut has_id = false;

        skip_whites!(self);

        loop {
            let tok = self.next_macro_token();
            match tok {
                MacroToken::None(s) => {
                    out.extend_from_slice(s);
                    last_kind = LastKind::None;
                }
                MacroToken::Id(id) => {
                    out.extend_from_slice(id.as_bytes());
                    last_kind = LastKind::Id;
                    has_id = true;
                }
                MacroToken::Space => {
                    if last_kind != LastKind::Space {
                        out.push(b' ');
                        last_kind = LastKind::Space;
                    }
                }
                MacroToken::WhiteStringify | MacroToken::Stringify | MacroToken::Concat => {}
                MacroToken::Eom => {
                    break;
                }
            }
        }

        MacroObject::new(out, has_id)
    }

    #[inline(always)]
    pub(crate) fn macro_final_eval(&mut self, out: &mut Vec<u8>, context: &PContext) {
        loop {
            let tok = self.next_macro_token();
            match tok {
                MacroToken::None(s) => {
                    out.extend_from_slice(s);
                }
                MacroToken::Id(id) => {
                    if !context.eval(&id, self, out) {
                        out.extend_from_slice(id.as_bytes());
                    }
                }
                MacroToken::Space => {
                    if let Some(last) = out.last() {
                        if *last != b' ' {
                            out.push(b' ');
                        }
                    } else {
                        out.push(b' ');
                    }
                }
                MacroToken::WhiteStringify | MacroToken::Stringify | MacroToken::Concat => {}
                MacroToken::Eom => {
                    break;
                }
            }
        }
    }

    #[inline(always)]
    pub(crate) fn macro_eval(&mut self, name: &str) -> bool {
        match self.context.get_type(name) {
            MacroType::None => {
                return false;
            }
            MacroType::Object(mac) => {
                mac.eval(&mut self.preproc_buf, &self.context);
            }
            MacroType::Function((n, va_args)) => {
                if let Some(args) = self.get_arguments(n, va_args.as_ref()) {
                    if let Macro::Function(mac) = self.context.get(name).unwrap() {
                        mac.eval_parsed_args(&args, &self.context, &mut self.preproc_buf);
                    }
                } else {
                    return false;
                }
            }
        }
        true
    }

    #[inline(always)]
    pub(crate) fn skip_until_else_endif(&mut self) {
        // skip until #else, #endif
        // need to lex to avoid to catch #else or #endif in a string, comment
        // or something like #define foo(else) #else (who want to do that ???)

        skip_whites!(self);
        if self.stop_skipping() {
            return;
        }

        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                self.pos += 1;

                let kind = unsafe { *PPCHARS.get_unchecked(c as usize) };
                match kind {
                    Kind::QUO => {
                        // we've a string or char literal
                        self.skip_by_delim(c);
                    }
                    Kind::RET => {
                        self.add_new_line();
                        skip_whites!(self);
                        // we've a new line so check if it starts with preproc directive
                        if self.stop_skipping() {
                            break;
                        }
                    }
                    Kind::SLA => {
                        self.skip_slash_or_not();
                    }
                    _ => {}
                }
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    fn stop_skipping(&mut self) -> bool {
        // we must be after a newline and skipped whites
        // the goal is to avoid to catch #define foo(else) #else
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'#' {
                // we've a hash at the beginning of a line
                self.pos += 1;
                skip_whites!(self);
                let id = self.get_preproc_keyword(false);
                match id {
                    Token::PreprocIf => self.get_if(IfKind::If),
                    Token::PreprocIfdef => self.get_if(IfKind::Ifdef),
                    Token::PreprocIfndef => self.get_if(IfKind::Ifndef),
                    Token::PreprocElif => self.get_elif(),
                    Token::PreprocElse => self.get_else(),
                    Token::PreprocEndif => self.get_endif(),
                    _ => false,
                }
            } else {
                false
            }
        } else {
            true
        }
    }

    #[inline(always)]
    pub(crate) fn get_if(&mut self, kind: IfKind) -> bool {
        let must_eval = if let Some(state) = self.context.if_state() {
            *state == IfState::Eval
        } else {
            true
        };

        if must_eval {
            skip_whites!(self);
            let condition = match kind {
                IfKind::If => {
                    let mut condition = Condition::new(self);
                    condition.eval_as_bool()
                }
                IfKind::Ifdef => {
                    let id = self.get_preproc_identifier();
                    self.context.defined(id)
                }
                IfKind::Ifndef => {
                    let id = self.get_preproc_identifier();
                    !self.context.defined(id)
                }
            };

            if condition {
                self.context.add_if(IfState::Eval);
                true
            } else {
                self.context.add_if(IfState::SkipAndSwitch);
                false
            }
        } else {
            self.context.add_if(IfState::Skip);
            false
        }
    }

    #[inline(always)]
    pub(crate) fn get_elif(&mut self) -> bool {
        // elif == else if
        if self.get_else() {
            self.get_if(IfKind::If)
        } else {
            false
        }
    }

    #[inline(always)]
    pub(crate) fn get_else(&mut self) -> bool {
        if let Some(state) = self.context.if_state() {
            match state {
                IfState::Eval => {
                    self.context.if_change(IfState::Skip);
                    false
                }
                IfState::Skip => false,
                IfState::SkipAndSwitch => {
                    self.context.if_change(IfState::Eval);
                    true
                }
            }
        } else {
            unreachable!();
        }
    }

    #[inline(always)]
    pub(crate) fn get_endif(&mut self) -> bool {
        if let Some(state) = self.context.if_state() {
            self.context.rm_if();
            if let Some(state) = self.context.if_state() {
                *state == IfState::Eval
            } else {
                true
            }
        } else {
            true
        }
    }

    #[inline(always)]
    pub(crate) fn get_define(&mut self) {
        skip_whites!(self);
        let name = self.get_preproc_identifier();
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'(' {
                self.pos += 1;
                let (args, va_args) = self.get_macro_arguments();
                let mac = self.get_function_definition(args, va_args);
                self.context.add_function(name.to_string(), mac);
            } else {
                skip_whites!(self);
                let obj = self.get_object_definition();
                self.context.add_object(name.to_string(), obj);
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_defined(&mut self) -> u64 {
        skip_whites!(self);
        if self.pos < self.len {
            let c = self.next_char(0);
            let name = if c == b'(' {
                self.pos += 1;
                skip_whites!(self);
                let name = self.get_preproc_identifier();
                skip_whites!(self);
                if self.pos < self.len {
                    let c = self.next_char(0);
                    if c == b')' {
                        self.pos += 1;
                    }
                }
                name
            } else {
                self.get_preproc_identifier()
            };
            return self.context.defined(name) as u64;
        }

        0
    }

    #[inline(always)]
    pub(crate) fn get_undef(&mut self) {
        skip_whites!(self);
        let name = self.get_preproc_identifier();
        self.context.undef(name);
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    macro_rules! mk_args {
        ( $( $a: expr ),* ) => {
            &vec![$( $a.as_bytes(), )*]
        }
    }

    #[test]
    fn test_include() {
        let mut p = Lexer::new(
            b"#include \"foo.h\"\n #include A(B)\n#  include_next      <foo\\barbar.h>\n",
        );

        assert_eq!(
            p.next(),
            Token::PreprocInclude(IncludeType::Quote(b"foo.h"))
        );
        assert_eq!(p.next(), Token::Eol);

        assert_eq!(p.next(), Token::PreprocInclude(IncludeType::Other(b"A(B)")));

        assert_eq!(
            p.next(),
            Token::PreprocIncludeNext(IncludeType::Angle(b"foo\\barbar.h"))
        );
        assert_eq!(p.next(), Token::Eol);
    }

    #[test]
    fn test_parse_args() {
        let mut p = Lexer::new(b"(abcd,efgh    \t , \t \t _ijkl , mno_123)");
        p.advance(1);
        let (map, _) = p.get_macro_arguments();
        let mut expected = HashMap::default();
        for (i, name) in vec!["abcd", "efgh", "_ijkl", "mno_123"].iter().enumerate() {
            expected.insert(*name, i);
        }

        assert_eq!(map, expected);

        let mut p = Lexer::new(b"()");
        p.advance(1);
        let (map, _) = p.get_macro_arguments();
        let mut expected = HashMap::default();

        assert_eq!(map, expected);

        let mut p = Lexer::new(b"(    )");
        p.advance(1);
        let (map, _) = p.get_macro_arguments();
        let mut expected = HashMap::default();

        assert_eq!(map, expected);
    }

    #[test]
    fn test_if_else() {
        let mut p = Lexer::new(
            concat!(
                "#define foo 37\n",
                "#if 1\n",
                "#define foo 56\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));

        let mut p = Lexer::new(
            concat!(
                "#define foo 37\n",
                "#if 0\n",
                "#define foo 56\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(37));

        let mut p = Lexer::new(
            concat!(
                "#define foo 37\n",
                "#if 0\n",
                "#define foo 56\n",
                "#else\n",
                "#define foo 78\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(78));

        let mut p = Lexer::new(
            concat!(
                "#define foo 37\n",
                "#if 1\n",
                "#define foo 56\n",
                "#else\n",
                "#define foo 78\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
    }

    #[test]
    fn test_if_else_nested() {
        let mut p = Lexer::new(
            concat!(
                "#define COND1 12\n",
                "#define COND2 0\n",
                "#define COND3 34\n",
                "\n",
                "#if COND1\n",
                "    #define foo 56\n",
                "    #if COND2\n",
                "        #define bar 78\n",
                "    #else\n",
                "       #if COND3\n",
                "           #define bar 910\n",
                "       #else\n",
                "           #define bar 1112\n",
                "       #endif\n",
                "    #endif\n",
                "#endif\n",
                "foo bar"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
        assert_eq!(p.next(), Token::LiteralInt(910));

        let mut p = Lexer::new(
            concat!(
                "#define COND1 12\n",
                "#define COND2\n",
                "#define COND3 34\n",
                "\n",
                "#if COND1\n",
                "    #define foo 56\n",
                "    #if defined(COND2)\n",
                "        #define bar 78\n",
                "    #else\n",
                "       #if COND3\n",
                "           #define bar 910\n",
                "       #else\n",
                "           #define bar 1112\n",
                "       #endif\n",
                "    #endif\n",
                "#endif\n",
                "foo bar"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
        assert_eq!(p.next(), Token::LiteralInt(78));

        let mut p = Lexer::new(
            concat!(
                "#define COND1 12\n",
                "\n",
                "#if COND1\n",
                "    #define foo 56\n",
                "    #if defined(COND2)\n",
                "        #define bar 78\n",
                "    #else\n",
                "       #if COND3\n",
                "           #define bar 910\n",
                "       #else\n",
                "           #define bar 1112\n",
                "       #endif\n",
                "    #endif\n",
                "#endif\n",
                "foo bar"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
        assert_eq!(p.next(), Token::LiteralInt(1112));
    }

    #[test]
    fn test_if_skip_first() {
        let mut p = Lexer::new(
            concat!(
                "#if A\n",
                "    #if B\n",
                "        #define foo 12\n",
                "    #else\n",
                "        #define foo 34\n",
                "    #endif\n",
                "#else\n",
                "    #define foo 56\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
    }

    #[test]
    fn test_elif() {
        let mut p = Lexer::new(
            concat!(
                "#define B 0\n",
                "#if A\n",
                "    #define foo 12\n",
                "#elif defined(B)\n",
                "    #define foo 56\n",
                "#endif\n",
                "foo"
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::LiteralInt(56));
    }
}
