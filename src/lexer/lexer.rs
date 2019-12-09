use bitflags::bitflags;
use phf::phf_map;

use super::number::get_decimal;
use super::pmacros::PContext;
use super::preprocessor::IncludeType;
use super::string::StringType;

bitflags! {
    struct Kind: u8 {
        const NON = 0;
        const IDE = 0b1;
        const KEY = 0b10;
        const NUM = 0b100;
        const UND = 0b1000;
    }
}

#[rustfmt::skip]
const CHARS: [Kind; 256] = [
    // 0 NUL   1 SOH      2 STX      3 ETX      4 EOT      5 ENQ      6 ACK      7 BEL
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 8 BS    9 HT       A NL       B VT       C NP       D CR       E SO       F SI
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 10 DLE  11 DC1     12 DC2     13 DC3     14 DC4     15 NAK     16 SYN     17 ETB
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 18 CAN  19 EM      1A SUB     1B ESC     1C FS      1D GS      1E RS      1F US
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 20 SP   21  !      22  "      23  #      24  $      25  %      26  &      27  '
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 28  (   29  )      2A  *      2B  +      2C  ,      2D  -      2E  .      2F   /
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 30  0   31  1      32  2      33  3      34  4      35  5      36  6      37  7
    Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, //
    // 38  8   39  9      3A  :      3B  ;      3C  <      3D  =      3E  >      3F  ?
    Kind::NUM, Kind::NUM, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 40  @   41  A      42  B      43  C      44  D      45  E      46  F      47  G
    Kind::NON, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 48  H   49  I      4A  J      4B  K      4C  L      4D  M      4E  N      4F  O
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 50  P   51  Q      52  R      53  S      54  T      55  U      56  V      57  W
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 58  X   59  Y      5A  Z      5B  [      5C  \      5D  ]      5E  ^      5F  _
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::NON, Kind::NON, Kind::NON, Kind::IDE, Kind::KEY, //
    // 60  `   61  a      62  b      63  c      64  d      65  e      66  f      67  g
    Kind::NON, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 68  h   69  i      6A  j      6B  k      6C  l      6D  m      6E  n      6F  o
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 70  p   71  q      72  r      73  s      74  t      75  u      76  v      77  w
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 78  x   79  y      7A  z      7B  {      7C  |      7D  }      7E  ~      7F DEL
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
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

static PREPROC_KEYWORDS: phf::Map<&'static str, Token<'_>> = phf_map! {
    "define" => Token::PreprocDefine,
    "elif" => Token::PreprocElif,
    "else" => Token::PreprocElse,
    "endif" => Token::PreprocEndif,
    "error" => Token::PreprocError,
    "if" => Token::PreprocIf,
    "ifdef" => Token::PreprocIfdef,
    "ifndef" => Token::PreprocIfndef,
    "include" => Token::PreprocInclude2,
    "include_next" => Token::PreprocIncludeNext2,
    "line" => Token::PreprocLine,
    "pragma" => Token::PreprocPragma,
    "undef" => Token::PreprocUndef,
};

static CPP_KEYWORDS: phf::Map<&'static str, Token<'_>> = phf_map! {
    "alignas" => Token::Alignas,
    "alignof" => Token::Alignof,
    "and" => Token::AndKw,
    "and_eq" => Token::AndEq,
    "asm" => Token::Asm,
    "auto" => Token::Auto,
    "bitand" => Token::BitAnd,
    "bitor" => Token::BitOr,
    "bool" => Token::Bool,
    "break" => Token::Break,
    "case" => Token::Case,
    "catch" => Token::Catch,
    "char" => Token::Char,
    "char16_t" => Token::Char16,
    "char32_t" => Token::Char32,
    "class" => Token::Class,
    "compl" => Token::Compl,
    "const" => Token::Const,
    "constexpr" => Token::Constexpr,
    "const_cast" => Token::ConstCast,
    "continue" => Token::Continue,
    "decltype" => Token::Decltype,
    "default" => Token::Default,
    "delete" => Token::Delete,
    "do" => Token::Do,
    "double" => Token::Double,
    "dynamic_cast" => Token::DynamicCast,
    "else" => Token::Else,
    "endif" => Token::Endif,
    "enum" => Token::Enum,
    "explicit" => Token::Explicit,
    "export" => Token::Export,
    "extern" => Token::Extern,
    "false" => Token::False,
    "final" => Token::Final,
    "float" => Token::Float,
    "for" => Token::For,
    "friend" => Token::Friend,
    "goto" => Token::Goto,
    "if" => Token::If,
    "inline" => Token::Inline,
    "int" => Token::Int,
    "long" => Token::Long,
    "mutable" => Token::Mutable,
    "namespace" => Token::Namespace,
    "new" => Token::New,
    "noexcept" => Token::Noexcept,
    "not" => Token::NotKw,
    "not_eq" => Token::NotEq,
    "nullptr" => Token::Nullptr,
    "operator" => Token::Operator,
    "or" => Token::OrKw,
    "or_eq" => Token::OrEq,
    "override" => Token::Override,
    "private" => Token::Private,
    "protected" => Token::Protected,
    "public" => Token::Public,
    "register" => Token::Register,
    "reinterpret_cast" => Token::ReinterpretCast,
    "restrict" => Token::Restrict,
    "return" => Token::Return,
    "short" => Token::Short,
    "signed" => Token::Signed,
    "sizeof" => Token::Sizeof,
    "static" => Token::Static,
    "static_assert" => Token::StaticAssert,
    "static_cast" => Token::StaticCast,
    "struct" => Token::Struct,
    "switch" => Token::Switch,
    "template" => Token::Template,
    "this" => Token::This,
    "thread_local" => Token::ThreadLocal,
    "throw" => Token::Throw,
    "true" => Token::True,
    "try" => Token::Try,
    "typedef" => Token::Typedef,
    "typeid" => Token::Typeid,
    "typename" => Token::TypeName,
    "union" => Token::Union,
    "unsigned" => Token::Unsigned,
    "using" => Token::Using,
    "virtual" => Token::Virtual,
    "void" => Token::Void,
    "volatile" => Token::Volatile,
    "wchar_t" => Token::Wchar,
    "while" => Token::While,
    "xor" => Token::XorKw,
    "xor_eq" => Token::XorEq,
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token<'a> {
    None,
    Eof,
    Eol,
    Comment(&'a [u8]),
    Not,
    NotEqual,
    Dollar,
    Modulo,
    ModuloEqual,
    AndAnd,
    And,
    AndEqual,
    LiteralChar(u32),
    LiteralLChar(u32),
    LiteralUUChar(u32),
    LiteralUChar(u32),
    LiteralU8Char(u32),
    LeftParen,
    RightParen,
    Star,
    StarEqual,
    PlusPlus,
    Plus,
    PlusEqual,
    Divide,
    DivideEqual,
    Comma,
    MinusMinus,
    Minus,
    MinusEqual,
    Arrow,
    ArrowStar,
    LiteralDecimal(f64),
    Dot,
    DotStar,
    Ellipsis,
    LiteralHex(u64),
    LiteralBin(u64),
    LiteralOct(u64),
    LiteralInt(u64),
    LiteralUInt(u64),
    LiteralLong(u64),
    LiteralLongLong(u64),
    LiteralULong(u64),
    LiteralULongLong(u64),
    LiteralString(&'a [u8]),
    LiteralLString(&'a [u8]),
    LiteralUString(&'a [u8]),
    LiteralUUString(&'a [u8]),
    LiteralU8String(&'a [u8]),
    LiteralRString(&'a [u8]),
    LiteralLRString(&'a [u8]),
    LiteralURString(&'a [u8]),
    LiteralUURString(&'a [u8]),
    LiteralU8RString(&'a [u8]),
    ColonColon,
    Colon,
    SemiColon,
    Lower,
    LowerEqual,
    LowerEqualGreater,
    LeftShift,
    LeftShiftEqual,
    EqualEqual,
    Equal,
    Greater,
    GreaterEqual,
    RightShift,
    RightShiftEqual,
    Question,
    At,
    Identifier(&'a str),
    LeftBrack,
    DoubleLeftBrack,
    Backslash,
    RightBrack,
    DoubleRightBrack,
    Xor,
    XorEqual,
    LeftBrace,
    OrOr,
    Or,
    OrEqual,
    RightBrace,
    Tilde,
    Alignas,
    Alignof,
    AndKw,
    AndEq,
    Asm,
    Auto,
    BitAnd,
    BitOr,
    Bool,
    Break,
    Case,
    Catch,
    Char,
    Char16,
    Char32,
    Class,
    Compl,
    Const,
    Constexpr,
    ConstCast,
    Continue,
    Decltype,
    Default,
    Delete,
    Do,
    Double,
    DynamicCast,
    Else,
    Endif,
    Enum,
    Explicit,
    Export,
    Extern,
    False,
    Final,
    Float,
    For,
    Friend,
    Goto,
    If,
    Inline,
    Int,
    Long,
    Mutable,
    Namespace,
    New,
    Noexcept,
    NotKw,
    NotEq,
    Nullptr,
    Operator,
    OrKw,
    OrEq,
    Override,
    Private,
    Protected,
    Public,
    Register,
    ReinterpretCast,
    Restrict,
    Return,
    Short,
    Signed,
    Sizeof,
    Static,
    StaticAssert,
    StaticCast,
    Struct,
    Switch,
    Template,
    This,
    ThreadLocal,
    Throw,
    True,
    Try,
    Typedef,
    Typeid,
    TypeName,
    Union,
    Unsigned,
    Using,
    Virtual,
    Void,
    Volatile,
    Wchar,
    While,
    XorKw,
    XorEq,
    PreprocIf,
    PreprocDefine,
    PreprocElif,
    PreprocElse,
    PreprocEndif,
    PreprocError,
    PreprocIfdef,
    PreprocIfndef,
    PreprocInclude(IncludeType<'a>),
    PreprocIncludeNext(IncludeType<'a>),
    PreprocInclude2,
    PreprocIncludeNext2,
    PreprocLine,
    PreprocPragma,
    PreprocUndef,
}

pub struct Lexer<'a> {
    pub preproc_buf: Vec<u8>,
    pub preproc_use: bool,
    pub sbuf: &'a [u8],
    pub slen: usize,
    pub spos: usize,
    pub buf: &'a [u8],
    pub len: usize,
    pub pos: usize,
    pub line: usize,
    pub lpos: usize,
    pub(crate) context: PContext,
}

macro_rules! get_operator {
    ($self: ident, $sym: expr, $single: ident, $double: ident, $equal: ident) => {{
        if $self.pos < $self.len {
            let c = unsafe { *$self.buf.get_unchecked($self.pos) };
            if c == $sym {
                $self.pos += 1;
                Token::$double
            } else if c == b'=' {
                $self.pos += 1;
                Token::$equal
            } else {
                Token::$single
            }
        } else {
            Token::$single
        }
    }};

    ($self: ident, $sym: expr, $single: ident, $double: ident) => {{
        if $self.pos < $self.len {
            let c = unsafe { *$self.buf.get_unchecked($self.pos) };
            if c == $sym {
                $self.pos += 1;
                Token::$double
            } else {
                Token::$single
            }
        } else {
            Token::$single
        }
    }};
}

macro_rules! get_basic_operator {
    ($self: ident, $sym: expr, $single: ident, $equal: ident) => {{
        if $self.pos < $self.len {
            let c = unsafe { *$self.buf.get_unchecked($self.pos) };
            if c == b'=' {
                $self.pos += 1;
                Token::$equal
            } else {
                Token::$single
            }
        } else {
            Token::$single
        }
    }};
}

impl<'a> Lexer<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            preproc_buf: Vec::new(),
            preproc_use: false,
            sbuf: &[],
            slen: 0,
            spos: 0,
            buf,
            len: buf.len(),
            pos: 0,
            line: 1,
            lpos: 0,
            context: PContext::default(),
        }
    }

    pub fn reset(&mut self) {
        self.pos = 0;
    }

    pub fn advance(&mut self, n: usize) {
        self.pos += n;
    }

    pub fn back(&mut self, n: usize) {
        self.pos -= n;
    }

    pub fn consume_tokens(&mut self, n: usize) {
        for _ in 0..n {
            self.next();
        }
    }

    pub(crate) fn add_new_line(&mut self) {
        self.line += 1;
        self.lpos = self.pos + 1;
    }

    pub(crate) fn get_line(&self) -> usize {
        self.line
    }

    pub(crate) fn get_column(&self) -> usize {
        self.pos - self.lpos + 1
    }

    #[inline(always)]
    pub(crate) fn next_char(&self, shift: usize) -> u8 {
        unsafe { *self.buf.get_unchecked(self.pos + shift) }
    }

    #[inline(always)]
    pub(crate) fn prev_char(&self, shift: usize) -> u8 {
        unsafe { *self.buf.get_unchecked(self.pos - shift) }
    }

    fn swap_buffers(&mut self) {
        if self.preproc_buf.is_empty() {
            return;
        }

        self.slen = self.len;
        self.len = self.preproc_buf.len();
        self.spos = self.pos;
        self.pos = 0;
        self.sbuf = self.buf;
        self.preproc_use = true;

        // TODO:
        // Probably not nice... but the preproc_buf will die with the Lexer and won't change when parsed
        // Check if we can do something better with a Pin (https://doc.rust-lang.org/std/pin/)
        self.buf = unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&self.preproc_buf) };
    }

    fn restore_buffers(&mut self) {
        self.pos = self.spos;
        self.len = self.slen;
        self.buf = self.sbuf;
        self.preproc_use = false;
        self.preproc_buf.clear();
    }

    pub(crate) fn show(&self) {
        println!(
            "...{}",
            std::str::from_utf8(&self.buf[self.pos..(self.pos + 10).min(self.len)]).unwrap()
        );
    }

    pub(crate) fn get_identifier(&mut self) -> Option<Token<'a>> {
        let id = self.get_identifier_str();
        if !self.preproc_use && self.macro_eval(id) {
            self.swap_buffers();
            None
        } else {
            Some(Token::Identifier(id))
        }
    }

    pub(crate) fn get_identifier_str(&mut self) -> &'a str {
        let spos = self.pos - 1;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::IDE | Kind::KEY | Kind::NUM) {
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }

        unsafe { std::str::from_utf8_unchecked(&self.buf.get_unchecked(spos..self.pos)) }
    }

    pub(crate) fn get_preproc_keyword(&mut self, eval: bool) -> Token<'a> {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::KEY) {
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }

        let id = unsafe { std::str::from_utf8_unchecked(&self.buf.get_unchecked(spos..self.pos)) };
        if let Some(keyword) = PREPROC_KEYWORDS.get(id) {
            if eval {
                self.preproc_parse(*keyword)
            } else {
                *keyword
            }
        } else {
            Token::Identifier(id)
        }
    }

    pub(crate) fn get_identifier_or_keyword(&mut self) -> Option<Token<'a>> {
        let spos = self.pos - 1;
        let mut keyword = true;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::KEY | Kind::IDE | Kind::NUM) {
                    break;
                }

                keyword = keyword && *kind == Kind::KEY;
                self.pos += 1;
            } else {
                break;
            }
        }

        let id = unsafe { std::str::from_utf8_unchecked(&self.buf.get_unchecked(spos..self.pos)) };
        if !self.preproc_use && self.macro_eval(id) {
            self.swap_buffers();
            None
        } else if keyword {
            if let Some(keyword) = CPP_KEYWORDS.get(id) {
                Some(*keyword)
            } else {
                Some(Token::Identifier(id))
            }
        } else {
            Some(Token::Identifier(id))
        }
    }

    pub(crate) fn get_exclamation(&mut self) -> Token<'a> {
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'=' {
                self.pos += 1;
                return Token::NotEqual;
            }
        }
        return Token::Not;
    }

    pub(crate) fn get_minus(&mut self) -> Token<'a> {
        let rem = self.len - self.pos;
        match rem {
            #[cold]
            0 => Token::Minus,
            #[cold]
            1 => {
                let c = self.next_char(0);
                if c == b'=' {
                    self.pos += 1;
                    Token::MinusEqual
                } else if c == b'-' {
                    self.pos += 1;
                    Token::MinusMinus
                } else if c == b'>' {
                    self.pos += 1;
                    Token::Arrow
                } else {
                    Token::Minus
                }
            }
            _ => {
                let c = self.next_char(0);
                if c == b'=' {
                    self.pos += 1;
                    Token::MinusEqual
                } else if c == b'-' {
                    self.pos += 1;
                    Token::MinusMinus
                } else if c == b'>' {
                    self.pos += 1;
                    let c = self.next_char(0);
                    if c == b'*' {
                        self.pos += 1;
                        Token::ArrowStar
                    } else {
                        Token::Arrow
                    }
                } else {
                    Token::Minus
                }
            }
        }
    }

    pub(crate) fn get_lower(&mut self) -> Token<'a> {
        let rem = self.len - self.pos;
        match rem {
            #[cold]
            0 => Token::Lower,
            #[cold]
            1 => {
                let c = self.next_char(0);
                if c == b'<' {
                    self.pos += 1;
                    Token::LeftShift
                } else if c == b'=' {
                    self.pos += 1;
                    Token::LowerEqual
                } else {
                    Token::Lower
                }
            }
            _ => {
                let c = self.next_char(0);
                if c == b'<' {
                    self.pos += 1;
                    let c = self.next_char(0);
                    if c == b'=' {
                        self.pos += 1;
                        Token::LeftShiftEqual
                    } else {
                        Token::LeftShift
                    }
                } else if c == b'=' {
                    self.pos += 1;
                    let c = self.next_char(0);
                    if c == b'>' {
                        self.pos += 1;
                        Token::LowerEqualGreater
                    } else {
                        Token::LowerEqual
                    }
                } else {
                    Token::Lower
                }
            }
        }
    }

    pub(crate) fn get_greater(&mut self) -> Token<'a> {
        let rem = self.len - self.pos;
        match rem {
            #[cold]
            0 => Token::Lower,
            #[cold]
            1 => {
                let c = self.next_char(0);
                if c == b'>' {
                    self.pos += 1;
                    Token::RightShift
                } else if c == b'=' {
                    self.pos += 1;
                    Token::GreaterEqual
                } else {
                    Token::Greater
                }
            }
            _ => {
                let c = self.next_char(0);
                if c == b'>' {
                    self.pos += 1;
                    let c = self.next_char(0);
                    if c == b'=' {
                        self.pos += 1;
                        Token::RightShiftEqual
                    } else {
                        Token::RightShift
                    }
                } else if c == b'=' {
                    self.pos += 1;
                    Token::GreaterEqual
                } else {
                    Token::Greater
                }
            }
        }
    }

    pub(crate) fn get_multiline_comment(&mut self) -> Token<'a> {
        self.pos += 1;
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                if c == b'/' {
                    let c = self.prev_char(1);
                    if c == b'*' {
                        let comment = unsafe { &self.buf.get_unchecked(spos..self.pos - 1) };
                        self.pos += 1;
                        return Token::Comment(comment);
                    }
                    self.pos += 1;
                } else if c == b'\n' {
                    self.add_new_line();
                    self.pos += 1;
                } else {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }

        let comment = unsafe { &self.buf.get_unchecked(spos..) };
        return Token::Comment(comment);
    }

    pub(crate) fn get_single_comment(&mut self) -> Token<'a> {
        let spos = self.pos + 1;
        self.pos += 1;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                self.pos += 1;
                if c == b'\\' {
                    self.pos += 1;
                } else if c == b'\n' {
                    self.add_new_line();
                    let comment = unsafe { &self.buf.get_unchecked(spos..self.pos - 1) };
                    return Token::Comment(comment);
                }
            } else {
                break;
            }
        }

        let comment = unsafe { &self.buf.get_unchecked(spos..) };
        return Token::Comment(comment);
    }

    pub(crate) fn get_slash(&mut self) -> Token<'a> {
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'/' {
                // Single line comment
                return self.get_single_comment();
            } else if c == b'*' {
                // Multiline comment
                return self.get_multiline_comment();
            } else if c == b'=' {
                self.pos += 1;
                return Token::DivideEqual;
            }
        }
        return Token::Divide;
    }

    pub(crate) fn get_backslash(&mut self) -> Option<Token<'a>> {
        if self.pos < self.len {
            let c = self.next_char(0);
            if c == b'\n' {
                // continuation line
                self.add_new_line();
                self.pos += 1;
                return None;
            }
        }
        Some(Token::Backslash)
    }

    pub(crate) fn get_preproc(&mut self) -> Token<'a> {
        skip_whites!(self);
        self.get_preproc_keyword(true)
    }

    pub(crate) fn next_useful(&mut self) -> Token<'a> {
        loop {
            match self.next() {
                Token::Comment(_) => {}
                tok => {
                    return tok;
                }
            }
        }
    }

    pub fn next(&mut self) -> Token<'a> {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                self.pos += 1;
                match c {
                    b'\t' => skip_whites!(self),
                    b'\n' => {
                        self.add_new_line();
                        // TODO: useless in general but useful to know the a #if condition is finished
                        // Probably remove it and find a way for the condition stuff
                        return Token::Eol;
                    }
                    b' ' => skip_whites!(self),
                    b'!' => {
                        return self.get_exclamation();
                    }
                    b'\"' => {
                        return self.get_string();
                    }
                    b'#' => {
                        self.get_preproc();
                    }
                    b'$' => {
                        return Token::Dollar;
                    }
                    b'%' => {
                        return get_basic_operator!(self, b'%', Modulo, ModuloEqual);
                    }
                    b'&' => {
                        return get_operator!(self, b'&', And, AndAnd, AndEqual);
                    }
                    b'\'' => {
                        return self.get_char();
                    }
                    b'(' => {
                        return Token::LeftParen;
                    }
                    b')' => {
                        return Token::RightParen;
                    }
                    b'*' => {
                        return get_basic_operator!(self, b'*', Star, StarEqual);
                    }
                    b'+' => {
                        return get_operator!(self, b'+', Plus, PlusPlus, PlusEqual);
                    }
                    b',' => {
                        return Token::Comma;
                    }
                    b'-' => {
                        return self.get_minus();
                    }
                    b'.' => {
                        return self.get_dot_or_number();
                    }
                    b'/' => {
                        return self.get_slash();
                    }
                    b'0'..=b'9' => {
                        return self.get_number(u64::from(c - b'0'));
                    }
                    b':' => {
                        return get_operator!(self, b':', Colon, ColonColon);
                    }
                    b';' => {
                        return Token::SemiColon;
                    }
                    b'<' => {
                        return self.get_lower();
                    }
                    b'=' => {
                        return get_operator!(self, b'=', Equal, EqualEqual);
                    }
                    b'>' => {
                        return self.get_greater();
                    }
                    b'?' => {
                        return Token::Question;
                    }
                    b'@' => {
                        return Token::At;
                    }
                    b'A'..=b'K' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'L' => {
                        if let Some(tok) = self.get_special_string_char(StringType::L) {
                            return tok;
                        } else if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'M'..=b'Q' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'R' => {
                        if let Some(tok) = self.get_special_string_char(StringType::R) {
                            return tok;
                        } else if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'S'..=b'T' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'U' => {
                        if let Some(tok) = self.get_special_string_char(StringType::UU) {
                            return tok;
                        } else if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'V'..=b'Z' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'[' => {
                        return get_operator!(self, b'[', LeftBrack, DoubleLeftBrack);
                    }
                    b'\\' => {
                        if let Some(tok) = self.get_backslash() {
                            return tok;
                        }
                    }
                    b']' => {
                        return get_operator!(self, b'[', RightBrack, DoubleRightBrack);
                    }
                    b'^' => {
                        return get_basic_operator!(self, b'^', Xor, XorEqual);
                    }
                    b'_' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
                    }
                    b'a'..=b't' => {
                        if let Some(tok) = self.get_identifier_or_keyword() {
                            return tok;
                        }
                    }
                    b'u' => {
                        if let Some(tok) = self.get_special_string_char(StringType::U) {
                            return tok;
                        } else if let Some(tok) = self.get_identifier_or_keyword() {
                            return tok;
                        }
                    }
                    b'v'..=b'z' => {
                        if let Some(tok) = self.get_identifier_or_keyword() {
                            return tok;
                        }
                    }
                    b'{' => {
                        return Token::LeftBrace;
                    }
                    b'|' => {
                        return get_operator!(self, b'|', Or, OrOr, OrEqual);
                    }
                    b'}' => {
                        return Token::RightBrace;
                    }
                    b'~' => {
                        return Token::Tilde;
                    }
                    _ => {}
                }
            } else if self.preproc_use {
                self.restore_buffers();
            } else {
                return Token::Eof;
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::fs;

    #[test]
    fn test_hex() {
        let mut p = Lexer::new(b"0x12345 0xabcdef 0XA1b2C3D4e5");
        assert_eq!(p.next(), Token::LiteralHex(0x12345));
        assert_eq!(p.next(), Token::LiteralHex(0xabcdef));
        assert_eq!(p.next(), Token::LiteralHex(0xa1b2c3d4e5));
    }

    #[test]
    fn test_oct() {
        let mut p = Lexer::new(b"012345 01357");
        assert_eq!(p.next(), Token::LiteralOct(0o12345));
        assert_eq!(p.next(), Token::LiteralOct(0o1357));
    }

    #[test]
    fn test_bin() {
        let mut p = Lexer::new(b"0b110001110010010110011101");
        assert_eq!(p.next(), Token::LiteralBin(0b110001110010010110011101));
    }

    #[test]
    fn test_number() {
        let mut p = Lexer::new(b"123 123e45 123e+45 123e-45");
        assert_eq!(p.next(), Token::LiteralInt(123));
        assert_eq!(p.next(), Token::LiteralDecimal(123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(123e-45));

        let mut p = Lexer::new(b"123. 123.e45 123.e+45 123.e-45");
        assert_eq!(p.next(), Token::LiteralDecimal(123.));
        assert_eq!(p.next(), Token::LiteralDecimal(123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(123e-45));

        let mut p = Lexer::new(b"123.456 123.456e78 123.456e+78 123.456e-78");
        assert_eq!(p.next(), Token::LiteralDecimal(123.456));
        assert_eq!(p.next(), Token::LiteralDecimal(123.456e78));
        assert_eq!(p.next(), Token::LiteralDecimal(123.456e78));
        assert_eq!(p.next(), Token::LiteralDecimal(123.456e-78));

        let mut p = Lexer::new(b"0.123 0.123e45 0.123e+45 0.123e-45");
        assert_eq!(p.next(), Token::LiteralDecimal(0.123));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e-45));

        let mut p = Lexer::new(b".123 .123e45 .123e+45 .123e-45");
        assert_eq!(p.next(), Token::LiteralDecimal(0.123));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e45));
        assert_eq!(p.next(), Token::LiteralDecimal(0.123e-45));

        let mut p = Lexer::new(b"0 0. .0 0.0");
        assert_eq!(p.next(), Token::LiteralInt(0));
        assert_eq!(p.next(), Token::LiteralDecimal(0.));
        assert_eq!(p.next(), Token::LiteralDecimal(0.));
        assert_eq!(p.next(), Token::LiteralDecimal(0.));

        let mut p = Lexer::new(b"123 123u 123U 123llu 123LLu 123llU 123LLU 123ull 123Ull 123ULL 123lu 123ul 123uL 123L");
        assert_eq!(p.next(), Token::LiteralInt(123));
        assert_eq!(p.next(), Token::LiteralUInt(123));
        assert_eq!(p.next(), Token::LiteralUInt(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULongLong(123));
        assert_eq!(p.next(), Token::LiteralULong(123));
        assert_eq!(p.next(), Token::LiteralULong(123));
        assert_eq!(p.next(), Token::LiteralULong(123));
        assert_eq!(p.next(), Token::LiteralLong(123));
    }

    #[test]
    fn test_keywords() {
        let mut p = Lexer::new(b"while foa whila for While For static_cast");
        assert_eq!(p.next(), Token::While);
        assert_eq!(p.next(), Token::Identifier("foa"));
        assert_eq!(p.next(), Token::Identifier("whila"));
        assert_eq!(p.next(), Token::For);
        assert_eq!(p.next(), Token::Identifier("While"));
        assert_eq!(p.next(), Token::Identifier("For"));
        assert_eq!(p.next(), Token::StaticCast);
    }

    #[test]
    fn test_identifiers() {
        let mut p =
            Lexer::new(b"hello world whilee Roo Lar uoo Uar u851 hello_world_WORLD_HELLO123");
        assert_eq!(p.next(), Token::Identifier("hello"));
        assert_eq!(p.next(), Token::Identifier("world"));
        assert_eq!(p.next(), Token::Identifier("whilee"));
        assert_eq!(p.next(), Token::Identifier("Roo"));
        assert_eq!(p.next(), Token::Identifier("Lar"));
        assert_eq!(p.next(), Token::Identifier("uoo"));
        assert_eq!(p.next(), Token::Identifier("Uar"));
        assert_eq!(p.next(), Token::Identifier("u851"));
        assert_eq!(p.next(), Token::Identifier("hello_world_WORLD_HELLO123"));
    }

    #[test]
    fn test_divide() {
        let mut p = Lexer::new(b"a / b");
        assert_eq!(p.next(), Token::Identifier("a"));
        assert_eq!(p.next(), Token::Divide);
        assert_eq!(p.next(), Token::Identifier("b"));
    }

    #[test]
    fn test_comment() {
        let mut p = Lexer::new(b"/* test */");
        assert_eq!(p.next(), Token::Comment(" test ".as_bytes()));
    }

    #[test]
    fn test_string() {
        let mut p = Lexer::new(b"\"foo\" \"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralString(b"foo"));
        assert_eq!(p.next(), Token::LiteralString(b"foo\\\"bar"));

        let mut p = Lexer::new(b"u\"foo\" u\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralUString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUString(b"foo\\\"bar"));

        let mut p = Lexer::new(b"U\"foo\" U\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralUUString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUUString(b"foo\\\"bar"));

        let mut p = Lexer::new(b"u8\"foo\" u8\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralU8String(b"foo"));
        assert_eq!(p.next(), Token::LiteralU8String(b"foo\\\"bar"));

        let mut p = Lexer::new(b"L\"foo\" L\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralLString(b"foo"));
        assert_eq!(p.next(), Token::LiteralLString(b"foo\\\"bar"));

        let mut p = Lexer::new(
            b"R\"hello(foo)hello\" R\"world(foo\n\\\"bar)world\" R\"world(foo)world  )world\"",
        );
        assert_eq!(p.next(), Token::LiteralRString(b"foo"));
        assert_eq!(p.next(), Token::LiteralRString(b"foo\n\\\"bar"));
        assert_eq!(p.next(), Token::LiteralRString(b"foo)world  "));

        let mut p = Lexer::new(b"LR\"hello(foo)hello\" UR\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next(), Token::LiteralLRString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUURString(b"foo\n\\\"bar"));

        let mut p = Lexer::new(b"uR\"hello(foo)hello\" u8R\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next(), Token::LiteralURString(b"foo"));
        assert_eq!(p.next(), Token::LiteralU8RString(b"foo\n\\\"bar"));
    }

    #[test]
    fn test_operators() {
        let mut p = Lexer::new(b"+ += ++ - -= -- -> / /= % %= | |= || & &= && ^ ^= * *= < <= > >= << <<= >> >>= = != == ! ~ ->* .* ... <=>");
        assert_eq!(p.next(), Token::Plus);
        assert_eq!(p.next(), Token::PlusEqual);
        assert_eq!(p.next(), Token::PlusPlus);
        assert_eq!(p.next(), Token::Minus);
        assert_eq!(p.next(), Token::MinusEqual);
        assert_eq!(p.next(), Token::MinusMinus);
        assert_eq!(p.next(), Token::Arrow);
        assert_eq!(p.next(), Token::Divide);
        assert_eq!(p.next(), Token::DivideEqual);
        assert_eq!(p.next(), Token::Modulo);
        assert_eq!(p.next(), Token::ModuloEqual);
        assert_eq!(p.next(), Token::Or);
        assert_eq!(p.next(), Token::OrEqual);
        assert_eq!(p.next(), Token::OrOr);
        assert_eq!(p.next(), Token::And);
        assert_eq!(p.next(), Token::AndEqual);
        assert_eq!(p.next(), Token::AndAnd);
        assert_eq!(p.next(), Token::Xor);
        assert_eq!(p.next(), Token::XorEqual);
        assert_eq!(p.next(), Token::Star);
        assert_eq!(p.next(), Token::StarEqual);
        assert_eq!(p.next(), Token::Lower);
        assert_eq!(p.next(), Token::LowerEqual);
        assert_eq!(p.next(), Token::Greater);
        assert_eq!(p.next(), Token::GreaterEqual);
        assert_eq!(p.next(), Token::LeftShift);
        assert_eq!(p.next(), Token::LeftShiftEqual);
        assert_eq!(p.next(), Token::RightShift);
        assert_eq!(p.next(), Token::RightShiftEqual);
        assert_eq!(p.next(), Token::Equal);
        assert_eq!(p.next(), Token::NotEqual);
        assert_eq!(p.next(), Token::EqualEqual);
        assert_eq!(p.next(), Token::Not);
        assert_eq!(p.next(), Token::Tilde);
        assert_eq!(p.next(), Token::ArrowStar);
        assert_eq!(p.next(), Token::DotStar);
        assert_eq!(p.next(), Token::Ellipsis);
        assert_eq!(p.next(), Token::LowerEqualGreater);
    }

    #[test]
    fn test_basic() {
        let mut p = Lexer::new(
            concat!(
                "#define foo(a,b) a##b\n",
                "foo(whi, le)\n",
                "#define foo(a,b) b##a\n",
                "foo(whi, le)\n",
                "#define foo bar foo\n",
                "foo\n",
            )
            .as_bytes(),
        );

        assert_eq!(p.next(), Token::While);
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Identifier("lewhi"));
        assert_eq!(p.next(), Token::Eol);
        assert_eq!(p.next(), Token::Identifier("bar"));
        assert_eq!(p.next(), Token::Identifier("foo"));
    }
}
