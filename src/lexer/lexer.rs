// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use phf::phf_map;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use super::buffer::{Buffer, BufferData};
use super::preprocessor::context::PreprocContext;
use super::preprocessor::include::PathIndex;
use super::source::{FileId, SourceMutex};
use super::string::StringType;
use crate::args;

#[derive(PartialEq)]
pub(super) enum Kind {
    NON,
    IDN,
    KEY,
}

#[rustfmt::skip]
pub(super) const CHARS: [Kind; 256] = [
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
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    // 38  8   39  9      3A  :      3B  ;      3C  <      3D  =      3E  >      3F  ?
    Kind::IDN, Kind::IDN, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 40  @   41  A      42  B      43  C      44  D      45  E      46  F      47  G
    Kind::NON, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    // 48  H   49  I      4A  J      4B  K      4C  L      4D  M      4E  N      4F  O
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    // 50  P   51  Q      52  R      53  S      54  T      55  U      56  V      57  W
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    // 58  X   59  Y      5A  Z      5B  [      5C  \      5D  ]      5E  ^      5F  _
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::NON, Kind::NON, Kind::NON, Kind::IDN, Kind::KEY, //
    // 60  `   61  a      62  b      63  c      64  d      65  e      66  f      67  g
    Kind::NON, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 68  h   69  i      6A  j      6B  k      6C  l      6D  m      6E  n      6F  o
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 70  p   71  q      72  r      73  s      74  t      75  u      76  v      77  w
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, Kind::KEY, //
    // 78  x   79  y      7A  z      7B  {      7C  |      7D  }      7E  ~      7F DEL
    Kind::KEY, Kind::KEY, Kind::KEY, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, Kind::IDN, //
];

static PREPROC_KEYWORDS: phf::Map<&'static str, Token> = phf_map! {
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

static CPP_KEYWORDS: phf::Map<&'static str, Token> = phf_map! {
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
    "__cdecl" => Token::Cdecl,
    "char" => Token::Char,
    "char8_t" => Token::Char8T,
    "char16_t" => Token::Char16T,
    "char32_t" => Token::Char32T,
    "class" => Token::Class,
    "__clrcall" => Token::Clrcall,
    "co_await" => Token::CoAwait,
    "co_return" => Token::CoReturn,
    "co_yield" => Token::CoYield,
    "compl" => Token::Compl,
    "concept" => Token::Concept,
    "const" => Token::Const,
    "consteval" => Token::Consteval,
    "constexpr" => Token::Constexpr,
    "constinit" => Token::Constinit,
    "const_cast" => Token::ConstCast,
    "continue" => Token::Continue,
    "_Complex" => Token::Complex,
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
    "__fastcall" => Token::Fastcall,
    "final" => Token::Final,
    "float" => Token::Float,
    "for" => Token::For,
    "friend" => Token::Friend,
    "__func__" => Token::Func,
    "__FUNCTION__" => Token::Function,
    "goto" => Token::Goto,
    "if" => Token::If,
    "_Imaginary" => Token::Imaginary,
    "import" => Token::Import,
    "inline" => Token::Inline,
    "int" => Token::Int,
    "long" => Token::Long,
    "module" => Token::Module,
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
    "__PRETTY_FUNCTION__" => Token::PrettyFunction,
    "private" => Token::Private,
    "protected" => Token::Protected,
    "public" => Token::Public,
    "requires" => Token::Requires,
    "register" => Token::Register,
    "reinterpret_cast" => Token::ReinterpretCast,
    "restrict" => Token::Restrict,
    "return" => Token::Return,
    "__restrict" => Token::MSRestrict,
    "short" => Token::Short,
    "signed" => Token::Signed,
    "sizeof" => Token::Sizeof,
    "__sptr" => Token::MSSptr,
    "static" => Token::Static,
    "static_assert" => Token::StaticAssert,
    "_Static_assert" => Token::CStaticAssert,
    "static_cast" => Token::StaticCast,
    "__stdcall" => Token::Stdcall,
    "struct" => Token::Struct,
    "switch" => Token::Switch,
    "template" => Token::Template,
    "this" => Token::This,
    "__thiscall" => Token::Thiscall,
    "thread_local" => Token::ThreadLocal,
    "throw" => Token::Throw,
    "true" => Token::True,
    "try" => Token::Try,
    "typedef" => Token::Typedef,
    "typeid" => Token::Typeid,
    "typename" => Token::Typename,
    "_unaligned" => Token::MS1Unaligned,
    "__unaligned" => Token::MSUnaligned,
    "union" => Token::Union,
    "unsigned" => Token::Unsigned,
    "__uptr" => Token::MSUptr,
    "using" => Token::Using,
    "__vectorcall" => Token::Vectorcall,
    "virtual" => Token::Virtual,
    "void" => Token::Void,
    "volatile" => Token::Volatile,
    "wchar_t" => Token::WcharT,
    "while" => Token::While,
    "xor" => Token::XorKw,
    "xor_eq" => Token::XorEq,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    None,
    Eof,
    Eol,
    Comment,
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
    LiteralCharUD(Box<(u32, String)>),
    LiteralLCharUD(Box<(u32, String)>),
    LiteralUUCharUD(Box<(u32, String)>),
    LiteralUCharUD(Box<(u32, String)>),
    LiteralU8CharUD(Box<(u32, String)>),
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
    LiteralFloatUD(Box<(f64, String)>),
    Dot,
    DotStar,
    Ellipsis,
    LiteralInt(u64),
    LiteralUInt(u64),
    LiteralLong(u64),
    LiteralLongLong(u64),
    LiteralULong(u64),
    LiteralULongLong(u64),
    LiteralIntUD(Box<(u64, String)>),
    LiteralString(String),
    LiteralLString(String),
    LiteralUString(String),
    LiteralUUString(String),
    LiteralU8String(String),
    LiteralRString(String),
    LiteralLRString(String),
    LiteralURString(String),
    LiteralUURString(String),
    LiteralU8RString(String),
    LiteralStringUD(Box<(String, String)>),
    LiteralLStringUD(Box<(String, String)>),
    LiteralUStringUD(Box<(String, String)>),
    LiteralUUStringUD(Box<(String, String)>),
    LiteralU8StringUD(Box<(String, String)>),
    LiteralRStringUD(Box<(String, String)>),
    LiteralLRStringUD(Box<(String, String)>),
    LiteralURStringUD(Box<(String, String)>),
    LiteralUURStringUD(Box<(String, String)>),
    LiteralU8RStringUD(Box<(String, String)>),
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
    Identifier(String),
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
    Cdecl,
    Char,
    Char8T,
    Char16T,
    Char32T,
    Class,
    Clrcall,
    CoAwait,
    CoReturn,
    CoYield,
    Compl,
    Complex,
    Concept,
    Const,
    Consteval,
    Constexpr,
    Constinit,
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
    Fastcall,
    Final,
    Float,
    For,
    Friend,
    Func,
    Function,
    Goto,
    If,
    Imaginary,
    Import,
    Inline,
    Int,
    Long,
    Module,
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
    PrettyFunction,
    Private,
    Protected,
    Public,
    Register,
    ReinterpretCast,
    Requires,
    Restrict,
    Return,
    Short,
    Signed,
    Sizeof,
    Static,
    StaticAssert,
    CStaticAssert,
    StaticCast,
    Stdcall,
    Struct,
    Switch,
    Template,
    This,
    Thiscall,
    ThreadLocal,
    Throw,
    True,
    Try,
    Typedef,
    Typeid,
    Typename,
    Union,
    Unsigned,
    Using,
    Vectorcall,
    Virtual,
    Void,
    Volatile,
    WcharT,
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
    MSRestrict,
    MSUptr,
    MSSptr,
    MS1Unaligned,
    MSUnaligned,
}

#[derive(Clone, Debug)]
pub struct Location {
    pub pos: usize,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Debug)]
pub struct LocToken {
    pub tok: Token,
    pub file: Option<FileId>,
    pub start: Location,
    pub end: Location,
}

impl LocToken {
    fn new(tok: Token, file: Option<FileId>, start: Location, end: Location) -> Self {
        Self {
            tok,
            file,
            start,
            end,
        }
    }
}

impl Token {
    pub(crate) fn get_string(self) -> Option<String> {
        match self {
            Self::LiteralString(s)
            | Self::LiteralLString(s)
            | Self::LiteralUString(s)
            | Self::LiteralUUString(s)
            | Self::LiteralU8String(s)
            | Self::LiteralRString(s)
            | Self::LiteralLRString(s)
            | Self::LiteralURString(s)
            | Self::LiteralUURString(s)
            | Self::LiteralU8RString(s) => Some(s),
            _ => None,
        }
    }
}

pub struct Lexer<'a, PC: PreprocContext> {
    pub(crate) buf: Buffer<'a>,
    pub(crate) context: PC,
    pub(crate) comment: Option<&'a [u8]>,
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

macro_rules! loc {
    ($self: ident, $tok: expr, $start: expr) => {{
        let tok = $tok;
        let end = $self.location();
        LocToken::new(tok, $self.buf.get_source_id(), $start, end)
    }};
}

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self {
            buf: Buffer::new(buf.to_vec(), FileId(0), PathIndex(0)),
            context: PC::default(),
            comment: None,
        }
    }

    pub fn new_with_context(buf: &'a [u8], source_id: FileId, context: PC) -> Self {
        Self {
            buf: Buffer::new(buf.to_vec(), source_id, PathIndex(0)),
            context,
            comment: None,
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

        if !cl.is_empty() {
            buffer.add_buffer(BufferData::new(cl, FileId(0), PathIndex(0)));
        }

        Self {
            buf: buffer,
            context,
            comment: None,
        }
    }

    pub fn get_comment(&self) -> &Option<&'a [u8]> {
        &self.comment
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
        while self.next().tok != Token::Eof {}
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

    pub(crate) fn get_identifier(&mut self) -> Option<Token> {
        let id = self.get_identifier_str();
        if !self.buf.preproc_use() && self.macro_eval(id) {
            self.buf.switch_to_preproc();
            None
        } else {
            Some(Token::Identifier(id.to_string()))
        }
    }

    pub(crate) fn get_identifier_str(&mut self) -> &'a str {
        let spos = self.buf.pos() - 1;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if *kind == Kind::NON {
                    break;
                }
                self.buf.inc();
            } else {
                break;
            }
        }

        unsafe { std::str::from_utf8_unchecked(&self.buf.slice(spos)) }
    }

    pub(crate) fn get_preproc_keyword(&mut self, eval: bool) -> Token {
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if *kind != Kind::KEY {
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
                self.preproc_parse(keyword.clone())
            } else {
                keyword.clone()
            }
        } else {
            Token::Identifier(id.to_string())
        }
    }

    pub(crate) fn get_identifier_or_keyword(&mut self) -> Option<Token> {
        let spos = self.buf.pos() - 1;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { CHARS.get_unchecked(c as usize) };
                if *kind == Kind::NON {
                    break;
                }

                self.buf.inc();
            } else {
                break;
            }
        }

        let id = unsafe { std::str::from_utf8_unchecked(&self.buf.slice(spos)) };
        if !self.buf.preproc_use() && self.macro_eval(id) {
            self.buf.switch_to_preproc();
            None
        } else if let Some(keyword) = CPP_KEYWORDS.get(id) {
            Some(keyword.clone())
        } else {
            Some(Token::Identifier(id.to_string()))
        }
    }

    pub(crate) fn get_exclamation(&mut self) -> Token {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'=' {
                self.buf.inc();
                return Token::NotEqual;
            }
        }
        Token::Not
    }

    pub(crate) fn get_minus(&mut self) -> Token {
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

    pub(crate) fn get_modulo(&mut self) -> Token {
        match self.buf.rem() {
            #[cold]
            0 => Token::Modulo,
            _ => {
                let c = self.buf.next_char();
                if c == b'=' {
                    self.buf.inc();
                    Token::ModuloEqual
                } else if c == b'>' {
                    self.buf.inc();
                    Token::RightBrace
                } else {
                    Token::Modulo
                }
            }
        }
    }

    pub(crate) fn get_lower(&mut self) -> Token {
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
                } else if c == b'%' {
                    self.buf.inc();
                    Token::LeftBrace
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
                } else if c == b'%' {
                    self.buf.inc();
                    Token::LeftBrace
                } else {
                    Token::Lower
                }
            }
        }
    }

    pub(crate) fn get_greater(&mut self) -> Token {
        match self.buf.rem() {
            #[cold]
            0 => Token::Greater,
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

    pub(crate) fn get_slash(&mut self) -> Token {
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
        Token::Divide
    }

    pub(crate) fn get_backslash(&mut self) -> Option<Token> {
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

    #[inline(always)]
    pub(crate) fn get_suffix(&mut self) -> Option<String> {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            let kind = unsafe { CHARS.get_unchecked(c as usize) };
            if *kind != Kind::NON {
                // we've a suffix
                self.buf.inc();
                Some(self.get_identifier_str().to_string())
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn get_preproc(&mut self) -> Token {
        skip_whites!(self);
        self.get_preproc_keyword(true)
    }

    pub(crate) fn steal_until(&mut self, term: Token) -> (LocToken, Vec<LocToken>) {
        let mut level = 0;
        let mut stole = Vec::with_capacity(64);
        loop {
            let tok = self.next_useful();
            match tok.tok {
                Token::LeftParen | Token::LeftBrack | Token::LeftBrace | Token::DoubleLeftBrack => {
                    level += 1;
                }
                Token::RightParen
                | Token::RightBrack
                | Token::RightBrace
                | Token::DoubleRightBrack => {
                    level -= 1;
                }
                _ => {}
            }

            if (tok.tok == term && level == 0) || tok.tok == Token::Eof {
                return (tok, stole);
            }

            stole.push(tok);
        }
    }

    pub(crate) fn next_useful(&mut self) -> LocToken {
        loop {
            let tok = self.next();
            match tok.tok {
                Token::Comment | Token::Eol => {}
                _ => {
                    return tok;
                }
            }
        }
    }

    fn location(&self) -> Location {
        Location {
            pos: self.buf.pos(),
            line: self.buf.get_line(),
            column: self.buf.get_column(),
        }
    }

    pub fn next(&mut self) -> LocToken {
        loop {
            let start = self.location();
            if self.buf.check_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                match c {
                    b'\t' => skip_whites!(self),
                    b'\n' => {
                        self.buf.add_new_line();
                        // TODO: useless in general but useful to know the a #if condition is finished
                        // Probably remove it and find a way for the condition stuff
                        return loc!(self, Token::Eol, start);
                    }
                    b' ' => skip_whites!(self),
                    b'!' => {
                        return loc!(self, self.get_exclamation(), start);
                    }
                    b'\"' => {
                        return loc!(self, self.get_string(StringType::None), start);
                    }
                    b'#' => {
                        return loc!(self, self.get_preproc(), start);
                    }
                    b'$' => {
                        return loc!(self, Token::Dollar, start);
                    }
                    b'%' => {
                        return loc!(self, self.get_modulo(), start);
                    }
                    b'&' => {
                        return loc!(
                            self,
                            get_operator!(self, b'&', And, AndAnd, AndEqual),
                            start
                        );
                    }
                    b'\'' => {
                        return loc!(self, self.get_char(StringType::None), start);
                    }
                    b'(' => {
                        return loc!(self, Token::LeftParen, start);
                    }
                    b')' => {
                        return loc!(self, Token::RightParen, start);
                    }
                    b'*' => {
                        return loc!(
                            self,
                            get_basic_operator!(self, b'*', Star, StarEqual),
                            start
                        );
                    }
                    b'+' => {
                        return loc!(
                            self,
                            get_operator!(self, b'+', Plus, PlusPlus, PlusEqual),
                            start
                        );
                    }
                    b',' => {
                        return loc!(self, Token::Comma, start);
                    }
                    b'-' => {
                        return loc!(self, self.get_minus(), start);
                    }
                    b'.' => {
                        return loc!(self, self.get_dot_or_number(), start);
                    }
                    b'/' => {
                        return loc!(self, self.get_slash(), start);
                    }
                    b'0'..=b'9' => {
                        return loc!(self, self.get_number(u64::from(c - b'0')), start);
                    }
                    b':' => {
                        return loc!(self, get_operator!(self, b':', Colon, ColonColon), start);
                    }
                    b';' => {
                        return loc!(self, Token::SemiColon, start);
                    }
                    b'<' => {
                        return loc!(self, self.get_lower(), start);
                    }
                    b'=' => {
                        return loc!(self, get_operator!(self, b'=', Equal, EqualEqual), start);
                    }
                    b'>' => {
                        return loc!(self, self.get_greater(), start);
                    }
                    b'?' => {
                        return loc!(self, Token::Question, start);
                    }
                    b'@' => {
                        return loc!(self, Token::At, start);
                    }
                    b'A'..=b'K' | b'M'..=b'Q' | b'S'..=b'T' | b'V'..=b'Z' => {
                        if let Some(tok) = self.get_identifier() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'L' => {
                        if let Some(tok) = self.get_special_string_char(StringType::L) {
                            return loc!(self, tok, start);
                        } else if let Some(tok) = self.get_identifier() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'R' => {
                        if let Some(tok) = self.get_special_string_char(StringType::R) {
                            return loc!(self, tok, start);
                        } else if let Some(tok) = self.get_identifier() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'U' => {
                        if let Some(tok) = self.get_special_string_char(StringType::UU) {
                            return loc!(self, tok, start);
                        } else if let Some(tok) = self.get_identifier() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'[' => {
                        return loc!(
                            self,
                            get_operator!(self, b'[', LeftBrack, DoubleLeftBrack),
                            start
                        );
                    }
                    b'\\' => {
                        if let Some(tok) = self.get_backslash() {
                            return loc!(self, tok, start);
                        }
                    }
                    b']' => {
                        return loc!(
                            self,
                            get_operator!(self, b']', RightBrack, DoubleRightBrack),
                            start
                        );
                    }
                    b'^' => {
                        return loc!(self, get_basic_operator!(self, b'^', Xor, XorEqual), start);
                    }
                    b'_' | b'a'..=b't' | b'v'..=b'z' => {
                        if let Some(tok) = self.get_identifier_or_keyword() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'u' => {
                        if let Some(tok) = self.get_special_string_char(StringType::U) {
                            return loc!(self, tok, start);
                        } else if let Some(tok) = self.get_identifier_or_keyword() {
                            return loc!(self, tok, start);
                        }
                    }
                    b'{' => {
                        return loc!(self, Token::LeftBrace, start);
                    }
                    b'|' => {
                        return loc!(self, get_operator!(self, b'|', Or, OrOr, OrEqual), start);
                    }
                    b'}' => {
                        return loc!(self, Token::RightBrace, start);
                    }
                    b'~' => {
                        return loc!(self, Token::Tilde, start);
                    }
                    b'\x7F'..=b'\xFF' => {
                        if let Some(tok) = self.get_identifier() {
                            return loc!(self, tok, start);
                        }
                    }
                    _ => {}
                }
            } else {
                return loc!(self, Token::Eof, start);
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
    fn test_keywords() {
        let mut p = Lexer::<DefaultContext>::new(b"while foa whila for While For static_cast");
        assert_eq!(p.next().tok, Token::While);
        assert_eq!(p.next().tok, Token::Identifier("foa".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("whila".to_string()));
        assert_eq!(p.next().tok, Token::For);
        assert_eq!(p.next().tok, Token::Identifier("While".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("For".to_string()));
        assert_eq!(p.next().tok, Token::StaticCast);
    }

    #[test]
    fn test_identifiers() {
        let mut p = Lexer::<DefaultContext>::new(
            b"hello world whilee Roo Lar uoo Uar u851 hello_world_WORLD_HELLO123",
        );
        assert_eq!(p.next().tok, Token::Identifier("hello".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("world".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("whilee".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("Roo".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("Lar".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("uoo".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("Uar".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("u851".to_string()));
        assert_eq!(
            p.next().tok,
            Token::Identifier("hello_world_WORLD_HELLO123".to_string())
        );
    }

    #[test]
    fn test_identifiers_utf8() {
        let mut p = Lexer::<DefaultContext>::new("🌹 🌵 🌻 🌷🌷🌷🌷🌷🌷".as_bytes());
        assert_eq!(p.next().tok, Token::Identifier("🌹".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("🌵".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("🌻".to_string()));
        assert_eq!(p.next().tok, Token::Identifier("🌷🌷🌷🌷🌷🌷".to_string()));
    }

    #[test]
    fn test_divide() {
        let mut p = Lexer::<DefaultContext>::new(b"a / b");
        assert_eq!(p.next().tok, Token::Identifier("a".to_string()));
        assert_eq!(p.next().tok, Token::Divide);
        assert_eq!(p.next().tok, Token::Identifier("b".to_string()));
    }

    #[test]
    fn test_operators() {
        let mut p = Lexer::<DefaultContext>::new(b"+ += ++ - -= -- -> / /= % %= | |= || & &= && ^ ^= * *= < <= > >= << <<= >> >>= = != == ! ~ ->* .* ... <=>");
        assert_eq!(p.next().tok, Token::Plus);
        assert_eq!(p.next().tok, Token::PlusEqual);
        assert_eq!(p.next().tok, Token::PlusPlus);
        assert_eq!(p.next().tok, Token::Minus);
        assert_eq!(p.next().tok, Token::MinusEqual);
        assert_eq!(p.next().tok, Token::MinusMinus);
        assert_eq!(p.next().tok, Token::Arrow);
        assert_eq!(p.next().tok, Token::Divide);
        assert_eq!(p.next().tok, Token::DivideEqual);
        assert_eq!(p.next().tok, Token::Modulo);
        assert_eq!(p.next().tok, Token::ModuloEqual);
        assert_eq!(p.next().tok, Token::Or);
        assert_eq!(p.next().tok, Token::OrEqual);
        assert_eq!(p.next().tok, Token::OrOr);
        assert_eq!(p.next().tok, Token::And);
        assert_eq!(p.next().tok, Token::AndEqual);
        assert_eq!(p.next().tok, Token::AndAnd);
        assert_eq!(p.next().tok, Token::Xor);
        assert_eq!(p.next().tok, Token::XorEqual);
        assert_eq!(p.next().tok, Token::Star);
        assert_eq!(p.next().tok, Token::StarEqual);
        assert_eq!(p.next().tok, Token::Lower);
        assert_eq!(p.next().tok, Token::LowerEqual);
        assert_eq!(p.next().tok, Token::Greater);
        assert_eq!(p.next().tok, Token::GreaterEqual);
        assert_eq!(p.next().tok, Token::LeftShift);
        assert_eq!(p.next().tok, Token::LeftShiftEqual);
        assert_eq!(p.next().tok, Token::RightShift);
        assert_eq!(p.next().tok, Token::RightShiftEqual);
        assert_eq!(p.next().tok, Token::Equal);
        assert_eq!(p.next().tok, Token::NotEqual);
        assert_eq!(p.next().tok, Token::EqualEqual);
        assert_eq!(p.next().tok, Token::Not);
        assert_eq!(p.next().tok, Token::Tilde);
        assert_eq!(p.next().tok, Token::ArrowStar);
        assert_eq!(p.next().tok, Token::DotStar);
        assert_eq!(p.next().tok, Token::Ellipsis);
        assert_eq!(p.next().tok, Token::LowerEqualGreater);
    }
}
