// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use hashbrown::HashMap;
use lazy_static::lazy_static;
use std::fs::{self, File};
use std::io::Read;
use std::path::PathBuf;
use std::sync::Arc;

use super::buffer::{Buffer, BufferData, Position};
use super::errors::LexerError;
use super::extra::SavedLexer;
use super::preprocessor::cache::IfCache;
use super::preprocessor::context::PreprocContext;
use super::preprocessor::include::PathIndex;
use super::source::{FileId, SourceMutex};
use super::string::StringType;
use crate::args;
use crate::errors::Span;

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
    Kind::IDN, Kind::IDN, Kind::IDN, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::KEY, //
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

macro_rules! mk_maps {
    ( $name: ident, $conv_name: ident, $test_name: ident, $( $tok_val: expr, $tok_name: path ), *) => {
        lazy_static! {
            static ref $name: HashMap<&'static str, Token> = {
                use Token::*;
                let mut map = HashMap::new();
                $(map.insert($tok_val, $tok_name);)*
                    map
            };
        }

        #[allow(dead_code)]
        pub fn $conv_name(tok: Token) -> &'static str {
            use Token::*;
            match tok {
                $($tok_name => $tok_val,)*
                    _ => unreachable!(),
            }
        }

        #[allow(dead_code)]
        pub fn $test_name() -> Vec<(&'static str, Token)> {
            use Token::*;

            vec![
                $(($tok_val, $tok_name),)*
            ]
        }
    }
}

mk_maps! {
    PREPROC_KEYWORDS, preproc_kw_to_str, test_preproc_kw,
    "define", PreprocDefine,
    "elif", PreprocElif,
    "else", PreprocElse,
    "endif", PreprocEndif,
    "error", PreprocError,
    "if", PreprocIf,
    "ifdef", PreprocIfdef,
    "ifndef", PreprocIfndef,
    "include", PreprocInclude,
    "include_next", PreprocIncludeNext,
    "line", PreprocLine,
    "pragma", PreprocPragma,
    "undef", PreprocUndef
}

// No keywords start with an uppercase letter
// If it happens then need to fix next_token
// first letters are:
// a, b, c, d, e, f, g, i, l, m, n, o, p, r, s, t, u, v, w, x and _
// So if there is some change then need to fix next_token too
mk_maps! {
    CPP_KEYWORDS, cpp_kw_to_str, test_cpp_kw,
    "alignas", Alignas,
    "alignof", Alignof,
    "and", AndKw,
    "and_eq", AndEq,
    "asm", Asm,
    "auto", Auto,
    "bitand", BitAnd,
    "bitor", BitOr,
    "bool", Bool,
    "break", Break,
    "case", Case,
    "catch", Catch,
    "__cdecl", Cdecl,
    "char", Char,
    "char8_t", Char8T,
    "char16_t", Char16T,
    "char32_t", Char32T,
    "class", Class,
    "__clrcall", Clrcall,
    "co_await", CoAwait,
    "co_return", CoReturn,
    "co_yield", CoYield,
    "compl", Compl,
    "concept", Concept,
    "const", Const,
    "consteval", Consteval,
    "constexpr", Constexpr,
    "constinit", Constinit,
    "const_cast", ConstCast,
    "continue", Continue,
    "_Complex", Complex,
    "decltype", Decltype,
    "default", Default,
    "delete", Delete,
    "do", Do,
    "double", Double,
    "dynamic_cast", DynamicCast,
    "else", Else,
    "endif", Endif,
    "enum", Enum,
    "explicit", Explicit,
    "export", Export,
    "extern", Extern,
    "false", False,
    "__fastcall", Fastcall,
    "final", Final,
    "float", Float,
    "for", For,
    "friend", Friend,
    "__func__", Func,
    "__FUNCTION__", Function,
    "goto", Goto,
    "if", If,
    "_Imaginary", Imaginary,
    "import", Import,
    "inline", Inline,
    "__inline", UInline,
    "__inline__", UInlineU,
    "int", Int,
    "long", Long,
    "module", Module,
    "mutable", Mutable,
    "namespace", Namespace,
    "new", New,
    "noexcept", Noexcept,
    "not", NotKw,
    "not_eq", NotEq,
    "nullptr", Nullptr,
    "operator", Operator,
    "or", OrKw,
    "or_eq", OrEq,
    "override", Override,
    "__PRETTY_FUNCTION__", PrettyFunction,
    "private", Private,
    "protected", Protected,
    "public", Public,
    "requires", Requires,
    "register", Register,
    "reinterpret_cast", ReinterpretCast,
    "restrict", Restrict,
    "return", Return,
    "__restrict", MSRestrict,
    "short", Short,
    "signed", Signed,
    "sizeof", Sizeof,
    "__sptr", MSSptr,
    "static", Static,
    "static_assert", StaticAssert,
    "_Static_assert", CStaticAssert,
    "static_cast", StaticCast,
    "__stdcall", Stdcall,
    "struct", Struct,
    "switch", Switch,
    "template", Template,
    "this", This,
    "__thiscall", Thiscall,
    "thread_local", ThreadLocal,
    "throw", Throw,
    "true", True,
    "try", Try,
    "typedef", Typedef,
    "typeid", Typeid,
    "typename", Typename,
    "_unaligned", MS1Unaligned,
    "__unaligned", MSUnaligned,
    "union", Union,
    "unsigned", Unsigned,
    "__uptr", MSUptr,
    "using", Using,
    "__vectorcall", Vectorcall,
    "virtual", Virtual,
    "void", Void,
    "volatile", Volatile,
    "wchar_t", WcharT,
    "while", While,
    "xor", XorKw,
    "xor_eq", XorEq
}

// TODO: group token by kind, for example put all the literal together
// it should speed up literal detection for example in using range
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
    UInline,
    UInlineU,
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

#[derive(Clone, Debug, Copy, Default)]
pub struct Location {
    pub pos: usize,
    pub line: u32,
    pub column: u32,
}

impl Location {
    fn dummy() -> Self {
        Self {
            pos: usize::max_value(),
            line: u32::max_value(),
            column: u32::max_value(),
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

pub trait TLexer {
    fn next_useful(&mut self) -> Token;

    fn save_until(&mut self, term: Token) -> (Token, SavedLexer) {
        let mut level = 0;

        // TODO: tune the capacity
        let mut stole = Vec::with_capacity(64);
        loop {
            let tok = self.next_useful();
            if (tok == term && level == 0) || tok == Token::Eof {
                stole.push(tok.clone());
                return (tok, SavedLexer::new(stole));
            }

            match tok {
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

            stole.push(tok);
        }
    }

    fn span(&self) -> Span;
}

pub struct Lexer<'a, PC: PreprocContext> {
    pub(crate) buf: Buffer<'a>,
    pub(crate) context: PC,
    pub(crate) comment: Option<&'a [u8]>,
    pub(crate) start: Location,
    pub(crate) errors: Vec<LexerError>,
}

impl<'a, PC: PreprocContext> TLexer for Lexer<'a, PC> {
    fn next_useful(&mut self) -> Token {
        loop {
            let tok = self.next_token();
            //eprintln!("{:?} -- {:?} -- {:?}", tok, self.span(), self.context.get_path(self.buf.get_source_id().unwrap()));
            match tok {
                Token::Comment | Token::Eol => {}
                _ => {
                    return tok;
                }
            }
        }
    }

    fn span(&self) -> Span {
        Span {
            file: self.buf.get_source_id(),
            start: self.start,
            end: self.location(),
        }
    }
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
            comment: None,
            start: Location::dummy(),
            errors: Vec::new(),
        }
    }

    pub fn new_with_context(buf: &'a [u8], source_id: FileId, context: PC) -> Self {
        Self {
            buf: Buffer::new(buf.to_vec(), source_id, PathIndex(0)),
            context,
            comment: None,
            start: Location::dummy(),
            errors: Vec::new(),
        }
    }

    pub fn new_from_file(
        file: &str,
        source: SourceMutex,
        if_cache: Arc<IfCache>,
        opt: args::PreprocOptions,
    ) -> Self {
        let path = PathBuf::from(file); //std::fs::canonicalize(file).unwrap();
                                        //let path = std::fs::canonicalize(file).unwrap();
        let file_size = fs::metadata(&path).map_or(1024 * 1024, |m| m.len() as usize);
        let mut file = File::open(&path).unwrap();
        let mut data = Vec::with_capacity(file_size + 1);
        file.read_to_end(&mut data).unwrap();

        let mut context = PC::new_with_if_cache(if_cache);
        context.set_source(source);
        let source_id = context.get_id(&path);
        let mut buffer = Buffer::new(data, source_id, PathIndex(0));

        context.set_sys_paths(&opt.sys_paths);

        let mut cl = Vec::with_capacity(16384);
        if opt.lang == args::Language::CPP {
            // TODO: be more smart here
            cl.extend_from_slice(b"#define __cplusplus 201703L\n");
        }
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
            start: Location::dummy(),
            errors: Vec::new(),
        }
    }

    pub fn get_comment(&self) -> &Option<&'a [u8]> {
        &self.comment
    }

    pub fn get_context(&self) -> &PC {
        &self.context
    }

    pub fn get_errors(&self) -> &[LexerError] {
        &self.errors
    }

    pub fn consume_tokens(&mut self, n: usize) {
        for _ in 0..n {
            self.next_token();
        }
    }

    pub fn consume_all(&mut self) {
        while self.next_token() != Token::Eof {}
    }

    pub fn get_line(&self) -> u32 {
        self.buf.get_line()
    }

    pub fn get_file(&self) -> PathBuf {
        self.context.get_path(self.buf.get_source_id().unwrap())
    }

    pub(crate) fn get_column(&self) -> u32 {
        self.buf.get_column()
    }

    pub fn debug(&self, msg: &str) {
        eprintln!(
            "DEBUG ({}): line {} in file ({:?}) {:?}",
            msg,
            self.get_line(),
            self.buf.get_source_id().unwrap(),
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

    pub(crate) fn get_preproc_keyword(&mut self, pos: Position) -> Token {
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
            if let Err(e) = self.preproc_parse(keyword.clone(), pos) {
                self.errors.push(e.clone());
                eprintln!("ERRRRRRRRRRor {:?}", e);
                Token::Eof
            } else {
                if cfg!(test) {
                    keyword.clone()
                } else {
                    Token::Eol
                }
            }
        } else {
            Token::Identifier(id.to_string())
        }
    }

    pub(crate) fn get_preproc_name(&mut self) -> &'a [u8] {
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

        &self.buf.slice(spos)
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

    pub(crate) fn get_preproc(&mut self, pos: Position) -> Token {
        skip_whites!(self);
        self.get_preproc_keyword(pos)
    }

    pub fn location(&self) -> Location {
        Location {
            pos: self.buf.pos(),
            line: self.buf.get_line(),
            column: self.buf.get_column(),
        }
    }

    pub fn next_token(&mut self) -> Token {
        loop {
            self.start = self.location();
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
                        return self.get_string(StringType::None);
                    }
                    b'#' => {
                        let mut pos = self.buf.raw_pos();
                        pos.pos -= 1;
                        return self.get_preproc(pos.clone());
                    }
                    b'$' => {
                        return Token::Dollar;
                    }
                    b'%' => {
                        return self.get_modulo();
                    }
                    b'&' => {
                        return get_operator!(self, b'&', And, AndAnd, AndEqual);
                    }
                    b'\'' => {
                        return self.get_char(StringType::None);
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
                    b'A'..=b'K' | b'M'..=b'Q' | b'S'..=b'T' | b'V'..=b'Z' => {
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
                    b'R' => {
                        if let Some(tok) = self.get_special_string_char(StringType::R) {
                            return tok;
                        } else if let Some(tok) = self.get_identifier() {
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
                    b'_' | b'a'..=b'g' | b'i' | b'l'..=b'p' | b'r'..=b't' | b'v'..=b'x' => {
                        if let Some(tok) = self.get_identifier_or_keyword() {
                            return tok;
                        }
                    }
                    b'h' | b'j' | b'k' | b'q' | b'y' | b'z' => {
                        if let Some(tok) = self.get_identifier() {
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
                    b'\x7F'..=b'\xFF' => {
                        if let Some(tok) = self.get_identifier() {
                            return tok;
                        }
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
    use pretty_assertions::assert_eq;

    #[test]
    fn test_keywords() {
        let mut p = Lexer::<DefaultContext>::new(b"while foa whila for While For static_cast");
        assert_eq!(p.next_token(), Token::While);
        assert_eq!(p.next_token(), Token::Identifier("foa".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("whila".to_string()));
        assert_eq!(p.next_token(), Token::For);
        assert_eq!(p.next_token(), Token::Identifier("While".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("For".to_string()));
        assert_eq!(p.next_token(), Token::StaticCast);
    }

    #[test]
    fn test_identifiers() {
        let mut p = Lexer::<DefaultContext>::new(
            b"hello world whilee Roo Lar uoo Uar u851 hello_world_WORLD_HELLO123",
        );
        assert_eq!(p.next_token(), Token::Identifier("hello".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("world".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("whilee".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("Roo".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("Lar".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("uoo".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("Uar".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("u851".to_string()));
        assert_eq!(
            p.next_token(),
            Token::Identifier("hello_world_WORLD_HELLO123".to_string())
        );
    }

    #[test]
    fn test_identifiers_utf8() {
        let mut p = Lexer::<DefaultContext>::new("🌹 🌵 🌻 🌷🌷🌷🌷🌷🌷".as_bytes());
        assert_eq!(p.next_token(), Token::Identifier("🌹".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("🌵".to_string()));
        assert_eq!(p.next_token(), Token::Identifier("🌻".to_string()));
        assert_eq!(
            p.next_token(),
            Token::Identifier("🌷🌷🌷🌷🌷🌷".to_string())
        );
    }

    #[test]
    fn test_divide() {
        let mut p = Lexer::<DefaultContext>::new(b"a / b");
        assert_eq!(p.next_token(), Token::Identifier("a".to_string()));
        assert_eq!(p.next_token(), Token::Divide);
        assert_eq!(p.next_token(), Token::Identifier("b".to_string()));
    }

    #[test]
    fn test_operators() {
        let mut p = Lexer::<DefaultContext>::new(b"+ += ++ - -= -- -> / /= % %= | |= || & &= && ^ ^= * *= < <= > >= << <<= >> >>= = != == ! ~ ->* .* ... <=>");
        assert_eq!(p.next_token(), Token::Plus);
        assert_eq!(p.next_token(), Token::PlusEqual);
        assert_eq!(p.next_token(), Token::PlusPlus);
        assert_eq!(p.next_token(), Token::Minus);
        assert_eq!(p.next_token(), Token::MinusEqual);
        assert_eq!(p.next_token(), Token::MinusMinus);
        assert_eq!(p.next_token(), Token::Arrow);
        assert_eq!(p.next_token(), Token::Divide);
        assert_eq!(p.next_token(), Token::DivideEqual);
        assert_eq!(p.next_token(), Token::Modulo);
        assert_eq!(p.next_token(), Token::ModuloEqual);
        assert_eq!(p.next_token(), Token::Or);
        assert_eq!(p.next_token(), Token::OrEqual);
        assert_eq!(p.next_token(), Token::OrOr);
        assert_eq!(p.next_token(), Token::And);
        assert_eq!(p.next_token(), Token::AndEqual);
        assert_eq!(p.next_token(), Token::AndAnd);
        assert_eq!(p.next_token(), Token::Xor);
        assert_eq!(p.next_token(), Token::XorEqual);
        assert_eq!(p.next_token(), Token::Star);
        assert_eq!(p.next_token(), Token::StarEqual);
        assert_eq!(p.next_token(), Token::Lower);
        assert_eq!(p.next_token(), Token::LowerEqual);
        assert_eq!(p.next_token(), Token::Greater);
        assert_eq!(p.next_token(), Token::GreaterEqual);
        assert_eq!(p.next_token(), Token::LeftShift);
        assert_eq!(p.next_token(), Token::LeftShiftEqual);
        assert_eq!(p.next_token(), Token::RightShift);
        assert_eq!(p.next_token(), Token::RightShiftEqual);
        assert_eq!(p.next_token(), Token::Equal);
        assert_eq!(p.next_token(), Token::NotEqual);
        assert_eq!(p.next_token(), Token::EqualEqual);
        assert_eq!(p.next_token(), Token::Not);
        assert_eq!(p.next_token(), Token::Tilde);
        assert_eq!(p.next_token(), Token::ArrowStar);
        assert_eq!(p.next_token(), Token::DotStar);
        assert_eq!(p.next_token(), Token::Ellipsis);
        assert_eq!(p.next_token(), Token::LowerEqualGreater);
    }

    #[test]
    fn test_for_cpp_kw() {
        for (s, tok) in test_cpp_kw().drain(..) {
            let mut p = Lexer::<DefaultContext>::new(s.as_bytes());
            assert_eq!(p.next_token(), tok);
        }
    }
}
