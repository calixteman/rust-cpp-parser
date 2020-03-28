use bitflags::bitflags;
use phf::phf_map;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use super::buffer::{Buffer, BufferData};
use super::preprocessor::context::PreprocContext;
use super::preprocessor::include::PathIndex;
use super::source::{self, FileId, SourceMutex};
use super::string::StringType;
use crate::args;

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
    "include" => Token::PreprocInclude,
    "include_next" => Token::PreprocIncludeNext,
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
    LiteralDouble(f64),
    LiteralFloat(f64),
    LiteralLongDouble(f64),
    Dot,
    DotStar,
    Ellipsis,
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
    PreprocInclude,
    PreprocIncludeNext,
    PreprocLine,
    PreprocPragma,
    PreprocUndef,
}

pub struct Lexer<'a, PC: PreprocContext> {
    pub(crate) buf: Buffer<'a>,
    pub(crate) context: PC,
}

macro_rules! get_operator {
    ($self: ident, $sym: expr, $single: ident, $double: ident, $equal: ident) => {{
        if $self.buf.has_char() {
            let c = $self.buf.next_char();
            if c == $sym {
                $self.buf.inc();
                Token::$double
            } else if c == b'=' {
                $self.buf.inc();
                Token::$equal
            } else {
                Token::$single
            }
        } else {
            Token::$single
        }
    }};

    ($self: ident, $sym: expr, $single: ident, $double: ident) => {{
        if $self.buf.has_char() {
            let c = $self.buf.next_char();
            if c == $sym {
                $self.buf.inc();
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
        if $self.buf.has_char() {
            let c = $self.buf.next_char();
            if c == b'=' {
                $self.buf.inc();
                Token::$equal
            } else {
                Token::$single
            }
        } else {
            Token::$single
        }
    }};
}

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf: Buffer::new(buf.to_vec(), FileId(0), PathIndex(0)),
            context: PC::default(),
        }
    }

    pub fn new_with_context(buf: &'a [u8], source_id: FileId, context: PC) -> Self {
        Self {
            buf: Buffer::new(buf.to_vec(), source_id, PathIndex(0)),
            context,
        }
    }

    pub fn new_from_file(file: &str, source: SourceMutex, opt: args::PreprocOptions) -> Self {
        let path = PathBuf::from(file); //std::fs::canonicalize(file).unwrap();
                                        //let path = std::fs::canonicalize(file).unwrap();
        let mut file = File::open(&path).unwrap();
        let mut data = Vec::new();
        file.read_to_end(&mut data).unwrap();

        let mut context = PC::default();
        context.set_source(source);
        let source_id = context.get_id(&path);
        let mut buffer = Buffer::new(data, source_id, PathIndex(0));

        context.set_sys_paths(&opt.sys_paths);

        let mut cl = Vec::new();
        for mac in opt.def.iter() {
            match mac {
                args::Macro::Defined((name, data)) => {
                    cl.extend_from_slice(b"#define ");
                    cl.extend_from_slice(name.as_bytes());
                    cl.push(b' ');
                    cl.extend_from_slice(data.as_bytes());
                    cl.push(b'\n');
                }
                args::Macro::Undef(name) => {
                    cl.extend_from_slice(b"#undef ");
                    cl.extend_from_slice(name.as_bytes());
                    cl.push(b'\n');
                }
            }
        }

        for inc in opt.includes.iter() {
            let path = PathBuf::from(inc);
            if path.is_relative() {
                let p = opt.current_dir.join(path);
                if p.exists() {
                    cl.extend_from_slice(b"#include \"");
                    cl.extend_from_slice(p.to_str().unwrap().as_bytes());
                    cl.push(b'\"');
                    cl.push(b'\n');
                    continue;
                }
            }
            cl.extend_from_slice(b"#include \"");
            cl.extend_from_slice(inc.as_bytes());
            cl.push(b'\"');
            cl.push(b'\n');
        }

        //eprintln!("FUCK\n{}", std::str::from_utf8(&cl).unwrap());

        if !cl.is_empty() {
            buffer.add_buffer(BufferData::new(cl, FileId(0), PathIndex(0)));
        }

        Self {
            buf: buffer,
            context,
        }
    }

    pub fn get_context(&self) -> &PC {
        &self.context
    }

    pub fn consume_tokens(&mut self, n: usize) {
        for _ in 0..n {
            self.next();
        }
    }

    pub fn consume_all(&mut self) {
        while self.next() != Token::Eof {}
    }

    pub fn get_line(&self) -> u32 {
        self.buf.get_line()
    }

    pub(crate) fn get_column(&self) -> u32 {
        self.buf.get_column()
    }

    pub fn debug(&self, msg: &str) {
        eprintln!(
            "DEBUG ({}): line {} in file {:?}",
            msg,
            self.get_line(),
            self.context.get_path(self.buf.get_source_id().unwrap())
        );
    }

    pub(crate) fn get_identifier(&mut self) -> Option<Token<'a>> {
        let id = self.get_identifier_str();
        if !self.buf.preproc_use() && self.macro_eval(id) {
            self.buf.switch_to_preproc();
            None
        } else {
            Some(Token::Identifier(id))
        }
    }

    pub(crate) fn get_identifier_str(&mut self) -> &'a str {
        let spos = self.buf.pos() - 1;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::IDE | Kind::KEY | Kind::NUM) {
                    break;
                }
                self.buf.inc();
            } else {
                break;
            }
        }

        unsafe { std::str::from_utf8_unchecked(&self.buf.slice(spos)) }
    }

    pub(crate) fn get_preproc_keyword(&mut self, eval: bool) -> Token<'a> {
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::KEY) {
                    break;
                }
                self.buf.inc();
            } else {
                break;
            }
        }

        let id = unsafe { std::str::from_utf8_unchecked(&self.buf.slice(spos)) };
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
        let spos = self.buf.pos() - 1;
        let mut keyword = true;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if !kind.intersects(Kind::KEY | Kind::IDE | Kind::NUM) {
                    break;
                }

                keyword = keyword && *kind == Kind::KEY;
                self.buf.inc();
            } else {
                break;
            }
        }

        let id = unsafe { std::str::from_utf8_unchecked(&self.buf.slice(spos)) };
        if !self.buf.preproc_use() && self.macro_eval(id) {
            self.buf.switch_to_preproc();
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
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'=' {
                self.buf.inc();
                return Token::NotEqual;
            }
        }
        return Token::Not;
    }

    pub(crate) fn get_minus(&mut self) -> Token<'a> {
        match self.buf.rem() {
            #[cold]
            0 => Token::Minus,
            #[cold]
            1 => {
                let c = self.buf.next_char();
                if c == b'=' {
                    self.buf.inc();
                    Token::MinusEqual
                } else if c == b'-' {
                    self.buf.inc();
                    Token::MinusMinus
                } else if c == b'>' {
                    self.buf.inc();
                    Token::Arrow
                } else {
                    Token::Minus
                }
            }
            _ => {
                let c = self.buf.next_char();
                if c == b'=' {
                    self.buf.inc();
                    Token::MinusEqual
                } else if c == b'-' {
                    self.buf.inc();
                    Token::MinusMinus
                } else if c == b'>' {
                    self.buf.inc();
                    let c = self.buf.next_char();
                    if c == b'*' {
                        self.buf.inc();
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
        match self.buf.rem() {
            #[cold]
            0 => Token::Lower,
            #[cold]
            1 => {
                let c = self.buf.next_char();
                if c == b'<' {
                    self.buf.inc();
                    Token::LeftShift
                } else if c == b'=' {
                    self.buf.inc();
                    Token::LowerEqual
                } else {
                    Token::Lower
                }
            }
            _ => {
                let c = self.buf.next_char();
                if c == b'<' {
                    self.buf.inc();
                    let c = self.buf.next_char();
                    if c == b'=' {
                        self.buf.inc();
                        Token::LeftShiftEqual
                    } else {
                        Token::LeftShift
                    }
                } else if c == b'=' {
                    self.buf.inc();
                    let c = self.buf.next_char();
                    if c == b'>' {
                        self.buf.inc();
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
        match self.buf.rem() {
            #[cold]
            0 => Token::Lower,
            #[cold]
            1 => {
                let c = self.buf.next_char();
                if c == b'>' {
                    self.buf.inc();
                    Token::RightShift
                } else if c == b'=' {
                    self.buf.inc();
                    Token::GreaterEqual
                } else {
                    Token::Greater
                }
            }
            _ => {
                let c = self.buf.next_char();
                if c == b'>' {
                    self.buf.inc();
                    let c = self.buf.next_char();
                    if c == b'=' {
                        self.buf.inc();
                        Token::RightShiftEqual
                    } else {
                        Token::RightShift
                    }
                } else if c == b'=' {
                    self.buf.inc();
                    Token::GreaterEqual
                } else {
                    Token::Greater
                }
            }
        }
    }

    pub(crate) fn get_slash(&mut self) -> Token<'a> {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'/' {
                // Single line comment
                return self.get_single_comment();
            } else if c == b'*' {
                // Multiline comment
                return self.get_multiline_comment();
            } else if c == b'=' {
                self.buf.inc();
                return Token::DivideEqual;
            }
        }
        return Token::Divide;
    }

    pub(crate) fn get_backslash(&mut self) -> Option<Token<'a>> {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'\n' {
                // continuation line
                self.buf.add_new_line();
                self.buf.inc();
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
            if self.buf.check_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                match c {
                    b'\t' => skip_whites!(self),
                    b'\n' => {
                        self.buf.add_new_line();
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
                        return self.get_preproc();
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
                        return get_operator!(self, b']', RightBrack, DoubleRightBrack);
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
            } else {
                return Token::Eof;
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use std::fs;

    #[test]
    fn test_hex() {
        let mut p = Lexer::<DefaultContext>::new(b"0x12345 0xabcdef 0XA'1b2'C3D'4e5 0xaB1ul");
        assert_eq!(p.next(), Token::LiteralInt(0x12345));
        assert_eq!(p.next(), Token::LiteralInt(0xabcdef));
        assert_eq!(p.next(), Token::LiteralInt(0xa1b2c3d4e5));
        assert_eq!(p.next(), Token::LiteralULong(0xab1));
    }

    #[test]
    fn test_oct() {
        let mut p = Lexer::<DefaultContext>::new(b"012345 01357 012'34ul");
        assert_eq!(p.next(), Token::LiteralInt(0o12345));
        assert_eq!(p.next(), Token::LiteralInt(0o1357));
        assert_eq!(p.next(), Token::LiteralULong(0o1234));
    }

    #[test]
    fn test_bin() {
        let mut p = Lexer::<DefaultContext>::new(b"0b110'001'110'010'010'110'011'101 0b1001ul");
        assert_eq!(p.next(), Token::LiteralInt(0b110001110010010110011101));
        assert_eq!(p.next(), Token::LiteralULong(0b1001));
    }

    #[test]
    fn test_number() {
        let mut p = Lexer::<DefaultContext>::new(b"123 123e45 123e+45 123e-45");
        assert_eq!(p.next(), Token::LiteralInt(123));
        assert_eq!(p.next(), Token::LiteralDouble(123e45));
        assert_eq!(p.next(), Token::LiteralDouble(123e45));
        assert_eq!(p.next(), Token::LiteralDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123. 123.e45 123.e+45 123.e-45");
        assert_eq!(p.next(), Token::LiteralDouble(123.));
        assert_eq!(p.next(), Token::LiteralDouble(123e45));
        assert_eq!(p.next(), Token::LiteralDouble(123e45));
        assert_eq!(p.next(), Token::LiteralDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123.f 123.e45F 123.e+45L 123.e-45l");
        assert_eq!(p.next(), Token::LiteralFloat(123.));
        assert_eq!(p.next(), Token::LiteralFloat(123e45));
        assert_eq!(p.next(), Token::LiteralLongDouble(123e45));
        assert_eq!(p.next(), Token::LiteralLongDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123.456 123.456e78 123.456e+78 123.456e-78 1.79769313486231570814527423731704357e+308L 2.2250738585072014e-308F");
        assert_eq!(p.next(), Token::LiteralDouble(123.456));
        assert_eq!(p.next(), Token::LiteralDouble(123.456e78));
        assert_eq!(p.next(), Token::LiteralDouble(123.456e78));
        assert_eq!(p.next(), Token::LiteralDouble(123.456e-78));
        assert_eq!(
            p.next(),
            Token::LiteralLongDouble(1.79769313486231570814527423731704357e+308)
        );
        assert_eq!(p.next(), Token::LiteralFloat(2.2250738585072014e-308));

        let mut p = Lexer::<DefaultContext>::new(b"0.123 0.123e45 0.123e+45 0.123e-45");
        assert_eq!(p.next(), Token::LiteralDouble(0.123));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e45));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e45));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e-45));

        let mut p = Lexer::<DefaultContext>::new(b".123 .123e45 .123e+45 .123e-45");
        assert_eq!(p.next(), Token::LiteralDouble(0.123));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e45));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e45));
        assert_eq!(p.next(), Token::LiteralDouble(0.123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"0 0. .0 0.0");
        assert_eq!(p.next(), Token::LiteralInt(0));
        assert_eq!(p.next(), Token::LiteralDouble(0.));
        assert_eq!(p.next(), Token::LiteralDouble(0.));
        assert_eq!(p.next(), Token::LiteralDouble(0.));

        let mut p = Lexer::<DefaultContext>::new(b"123 123u 123U 123llu 123LLu 123llU 123LLU 123ull 123Ull 123ULL 123lu 123ul 123uL 123L");
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

        let mut p = Lexer::<DefaultContext>::new(b"0x1.2p3 0x1.2p3F 0xA.Bp-1 0XAB1P-3");
        assert_eq!(p.next(), Token::LiteralDouble(9.0));
        assert_eq!(p.next(), Token::LiteralFloat(9.0));
        assert_eq!(p.next(), Token::LiteralDouble(5.34375));
        assert_eq!(p.next(), Token::LiteralDouble(342.125));
    }

    #[test]
    fn test_keywords() {
        let mut p = Lexer::<DefaultContext>::new(b"while foa whila for While For static_cast");
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
        let mut p = Lexer::<DefaultContext>::new(
            b"hello world whilee Roo Lar uoo Uar u851 hello_world_WORLD_HELLO123",
        );
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
        let mut p = Lexer::<DefaultContext>::new(b"a / b");
        assert_eq!(p.next(), Token::Identifier("a"));
        assert_eq!(p.next(), Token::Divide);
        assert_eq!(p.next(), Token::Identifier("b"));
    }

    #[test]
    fn test_comment() {
        let mut p = Lexer::<DefaultContext>::new(b"/* test */");
        assert_eq!(p.next(), Token::Comment(" test ".as_bytes()));
    }

    #[test]
    fn test_string() {
        let mut p = Lexer::<DefaultContext>::new(b"\"foo\" \"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralString(b"foo"));
        assert_eq!(p.next(), Token::LiteralString(b"foo\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(b"u\"foo\" u\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralUString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUString(b"foo\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(b"U\"foo\" U\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralUUString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUUString(b"foo\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(b"u8\"foo\" u8\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralU8String(b"foo"));
        assert_eq!(p.next(), Token::LiteralU8String(b"foo\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(b"L\"foo\" L\"foo\\\"bar\"");
        assert_eq!(p.next(), Token::LiteralLString(b"foo"));
        assert_eq!(p.next(), Token::LiteralLString(b"foo\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(
            b"R\"hello(foo)hello\" R\"world(foo\n\\\"bar)world\" R\"world(foo)world  )world\"",
        );
        assert_eq!(p.next(), Token::LiteralRString(b"foo"));
        assert_eq!(p.next(), Token::LiteralRString(b"foo\n\\\"bar"));
        assert_eq!(p.next(), Token::LiteralRString(b"foo)world  "));

        let mut p =
            Lexer::<DefaultContext>::new(b"LR\"hello(foo)hello\" UR\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next(), Token::LiteralLRString(b"foo"));
        assert_eq!(p.next(), Token::LiteralUURString(b"foo\n\\\"bar"));

        let mut p =
            Lexer::<DefaultContext>::new(b"uR\"hello(foo)hello\" u8R\"world(foo\n\\\"bar)world\"");
        assert_eq!(p.next(), Token::LiteralURString(b"foo"));
        assert_eq!(p.next(), Token::LiteralU8RString(b"foo\n\\\"bar"));

        let mut p = Lexer::<DefaultContext>::new(b"R\"(abc)\ndef)\n)\"");
        assert_eq!(p.next(), Token::LiteralRString(b"abc)\ndef)\n"));
    }

    #[test]
    fn test_operators() {
        let mut p = Lexer::<DefaultContext>::new(b"+ += ++ - -= -- -> / /= % %= | |= || & &= && ^ ^= * *= < <= > >= << <<= >> >>= = != == ! ~ ->* .* ... <=>");
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
}
