use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

#[derive(Clone, Debug, PartialEq)]
pub struct Attribute {
    pub namespace: Option<String>,
    pub name: String,
    pub arg: Option<AttributeArg>,
    pub has_using: bool,
}

pub type Attributes = Vec<Attribute>;

struct UsingParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> UsingParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self) -> (Option<LocToken<'a>>, Option<String>) {
        let tok = self.lexer.next_useful();
        match tok.tok {
            Token::Using => {
                let tok = self.lexer.next_useful();
                if let Token::Identifier(ns) = tok.tok {
                    let ns = Some(ns.to_string());
                    let tok = self.lexer.next_useful();
                    match tok.tok {
                        Token::Colon => {
                            return (None, ns);
                        }
                        _ => {
                            unreachable!("Invalid token in attributes: {:?}", tok);
                        }
                    }
                } else {
                    unreachable!("Invalid token in attributes: {:?}", tok);
                }
            }
            _ => {}
        }
        (Some(tok), None)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AttributeArg {
    pub tokens: Vec<Token<'static>>,
    buf: Box<Vec<u8>>,
}

struct AttributeArgTemp {
    tokens: Vec<Token<'static>>,
    buf: Vec<u8>,
    lens: Vec<(usize, usize, usize)>,
}

impl AttributeArgTemp {
    fn new() -> Self {
        Self {
            tokens: Vec::new(),
            buf: Vec::with_capacity(256),
            lens: Vec::new(),
        }
    }

    fn add_tok<'b>(&mut self, tok: Token<'b>) {
        use Token::*;

        let tk = match tok {
            Comment(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                Comment(b"")
            }
            LiteralString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralString(b"")
            }
            LiteralLString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralLString(b"")
            }
            LiteralUString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralUString(b"")
            }
            LiteralUUString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralUUString(b"")
            }
            LiteralU8String(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralU8String(b"")
            }
            LiteralRString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralRString(b"")
            }
            LiteralLRString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralLRString(b"")
            }
            LiteralURString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralURString(b"")
            }
            LiteralUURString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralUURString(b"")
            }
            LiteralU8RString(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s);
                LiteralU8RString(b"")
            }
            Identifier(s) => {
                self.lens.push((self.tokens.len(), self.buf.len(), s.len()));
                self.buf.extend_from_slice(s.as_bytes());
                Identifier("")
            }
            None => None,
            Eof => Eof,
            Eol => Eol,
            Not => Not,
            NotEqual => NotEqual,
            Dollar => Dollar,
            Modulo => Modulo,
            ModuloEqual => ModuloEqual,
            AndAnd => AndAnd,
            And => And,
            AndEqual => AndEqual,
            LiteralChar(x) => LiteralChar(x),
            LiteralLChar(x) => LiteralLChar(x),
            LiteralUUChar(x) => LiteralUUChar(x),
            LiteralUChar(x) => LiteralUChar(x),
            LiteralU8Char(x) => LiteralU8Char(x),
            LeftParen => LeftParen,
            RightParen => RightParen,
            Star => Star,
            StarEqual => StarEqual,
            PlusPlus => PlusPlus,
            Plus => Plus,
            PlusEqual => PlusEqual,
            Divide => Divide,
            DivideEqual => DivideEqual,
            Comma => Comma,
            MinusMinus => MinusMinus,
            Minus => Minus,
            MinusEqual => MinusEqual,
            Arrow => Arrow,
            ArrowStar => ArrowStar,
            LiteralDouble(x) => LiteralDouble(x),
            LiteralFloat(x) => LiteralFloat(x),
            LiteralLongDouble(x) => LiteralLongDouble(x),
            Dot => Dot,
            DotStar => DotStar,
            Ellipsis => Ellipsis,
            LiteralInt(x) => LiteralInt(x),
            LiteralUInt(x) => LiteralUInt(x),
            LiteralLong(x) => LiteralLong(x),
            LiteralLongLong(x) => LiteralLongLong(x),
            LiteralULong(x) => LiteralULong(x),
            LiteralULongLong(x) => LiteralULongLong(x),
            ColonColon => ColonColon,
            Colon => Colon,
            SemiColon => SemiColon,
            Lower => Lower,
            LowerEqual => LowerEqual,
            LowerEqualGreater => LowerEqualGreater,
            LeftShift => LeftShift,
            LeftShiftEqual => LeftShiftEqual,
            EqualEqual => EqualEqual,
            Equal => Equal,
            Greater => Greater,
            GreaterEqual => GreaterEqual,
            RightShift => RightShift,
            RightShiftEqual => RightShiftEqual,
            Question => Question,
            At => At,
            LeftBrack => LeftBrack,
            DoubleLeftBrack => DoubleLeftBrack,
            Backslash => Backslash,
            RightBrack => RightBrack,
            DoubleRightBrack => DoubleRightBrack,
            Xor => Xor,
            XorEqual => XorEqual,
            LeftBrace => LeftBrace,
            OrOr => OrOr,
            Or => Or,
            OrEqual => OrEqual,
            RightBrace => RightBrace,
            Tilde => Tilde,
            Alignas => Alignas,
            Alignof => Alignof,
            AndKw => AndKw,
            AndEq => AndEq,
            Asm => Asm,
            Auto => Auto,
            BitAnd => BitAnd,
            BitOr => BitOr,
            Bool => Bool,
            Break => Break,
            Case => Case,
            Catch => Catch,
            Char => Char,
            Char8T => Char8T,
            Char16T => Char16T,
            Char32T => Char32T,
            Class => Class,
            Compl => Compl,
            Complex => Complex,
            Const => Const,
            Consteval => Consteval,
            Constexpr => Constexpr,
            Constinit => Constinit,
            ConstCast => ConstCast,
            Continue => Continue,
            Decltype => Decltype,
            Default => Default,
            Delete => Delete,
            Do => Do,
            Double => Double,
            DynamicCast => DynamicCast,
            Else => Else,
            Endif => Endif,
            Enum => Enum,
            Explicit => Explicit,
            Export => Export,
            Extern => Extern,
            False => False,
            Final => Final,
            Float => Float,
            For => For,
            Friend => Friend,
            Goto => Goto,
            If => If,
            Imaginary => Imaginary,
            Inline => Inline,
            Int => Int,
            Long => Long,
            Mutable => Mutable,
            Namespace => Namespace,
            New => New,
            Noexcept => Noexcept,
            NotKw => NotKw,
            NotEq => NotEq,
            Nullptr => Nullptr,
            Operator => Operator,
            OrKw => OrKw,
            OrEq => OrEq,
            Override => Override,
            Private => Private,
            Protected => Protected,
            Public => Public,
            Register => Register,
            ReinterpretCast => ReinterpretCast,
            Restrict => Restrict,
            Return => Return,
            Short => Short,
            Signed => Signed,
            Sizeof => Sizeof,
            Static => Static,
            StaticAssert => StaticAssert,
            StaticCast => StaticCast,
            Struct => Struct,
            Switch => Switch,
            Template => Template,
            This => This,
            ThreadLocal => ThreadLocal,
            Throw => Throw,
            True => True,
            Try => Try,
            Typedef => Typedef,
            Typeid => Typeid,
            TypeName => TypeName,
            Union => Union,
            Unsigned => Unsigned,
            Using => Using,
            Virtual => Virtual,
            Void => Void,
            Volatile => Volatile,
            WcharT => WcharT,
            While => While,
            XorKw => XorKw,
            XorEq => XorEq,
            PreprocIf => PreprocIf,
            PreprocDefine => PreprocDefine,
            PreprocElif => PreprocElif,
            PreprocElse => PreprocElse,
            PreprocEndif => PreprocEndif,
            PreprocError => PreprocError,
            PreprocIfdef => PreprocIfdef,
            PreprocIfndef => PreprocIfndef,
            PreprocInclude => PreprocInclude,
            PreprocIncludeNext => PreprocIncludeNext,
            PreprocLine => PreprocLine,
            PreprocPragma => PreprocPragma,
            PreprocUndef => PreprocUndef,
        };
        self.tokens.push(tk);
    }

    fn finalize(self) -> AttributeArg {
        use Token::*;

        let mut args = AttributeArg {
            tokens: self.tokens,
            buf: Box::new(self.buf),
        };

        for (pos, start, end) in self.lens {
            // TODO: I'm not super happy with that...
            // I tryed tio play around std::pin::Pin without any success
            let s = unsafe {
                &*std::mem::transmute::<&[u8], *const [u8]>(&args.buf.get_unchecked(start..end))
            };

            match args.tokens[pos] {
                Comment(_) => {
                    args.tokens[pos] = Comment(s);
                }
                LiteralString(_) => {
                    args.tokens[pos] = LiteralString(s);
                }
                LiteralLString(_) => {
                    args.tokens[pos] = LiteralLString(s);
                }
                LiteralUString(_) => {
                    args.tokens[pos] = LiteralUString(s);
                }
                LiteralUUString(_) => {
                    args.tokens[pos] = LiteralUUString(s);
                }
                LiteralU8String(_) => {
                    args.tokens[pos] = LiteralU8String(s);
                }
                LiteralRString(_) => {
                    args.tokens[pos] = LiteralRString(s);
                }
                LiteralLRString(_) => {
                    args.tokens[pos] = LiteralLRString(s);
                }
                LiteralURString(_) => {
                    args.tokens[pos] = LiteralURString(s);
                }
                LiteralUURString(_) => {
                    args.tokens[pos] = LiteralUURString(s);
                }
                LiteralU8RString(_) => {
                    args.tokens[pos] = LiteralU8RString(s);
                }
                Identifier(_) => unsafe {
                    args.tokens[pos] = Identifier(std::str::from_utf8_unchecked(s));
                },
                _ => {}
            }
        }

        args
    }
}

struct ArgumentParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ArgumentParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken<'a>>) -> (Option<LocToken<'a>>, Option<AttributeArg>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftParen {
            return (Some(tok), None);
        }

        let mut arg = AttributeArgTemp::new();
        let mut paren_count = 1;
        let mut brack_count = 0;
        let mut brace_count = 0;

        loop {
            let tok = self.lexer.next_useful();
            match tok.tok {
                Token::LeftParen => {
                    paren_count += 1;
                }
                Token::RightParen => {
                    if paren_count == 1 {
                        if brack_count != 0 || brace_count != 0 {
                            unreachable!("Unbalanced attribute");
                        } else {
                            let arg = arg.finalize();
                            return (None, Some(arg));
                        }
                    } else {
                        paren_count -= 1;
                    }
                }
                Token::LeftBrack => {
                    brack_count += 1;
                }
                Token::RightBrack => {
                    if brack_count == 0 {
                        unreachable!("Unbalanced attribute");
                    } else {
                        brack_count -= 1;
                    }
                }
                Token::LeftBrace => {
                    brace_count += 1;
                }
                Token::RightBrace => {
                    if brace_count == 0 {
                        unreachable!("Unbalanced attribute");
                    } else {
                        brace_count -= 1;
                    }
                }
                Token::Eof => {
                    unreachable!("Wrong attribute");
                }
                t => {
                    arg.add_tok(t);
                }
            }
        }
    }
}

struct NameParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> NameParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: LocToken<'a>) -> (Option<LocToken<'a>>, (Option<String>, String)) {
        match tok.tok {
            Token::Identifier(id) => {
                let id = id.to_string();
                let tk = self.lexer.next_useful();
                if tk.tok == Token::ColonColon {
                    let ns = Some(id);
                    let tk = self.lexer.next_useful();
                    if let Token::Identifier(id) = tk.tok {
                        (None, (ns, id.to_string()))
                    } else {
                        unreachable!("Invalid token in attributes: {:?}", tk);
                    }
                } else {
                    (Some(tk), (None, id))
                }
            }
            _ => {
                unreachable!("Invalid token in attributes: {:?}", tok);
            }
        }
    }
}

struct AttributeParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> AttributeParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(
        self,
        attributes: &mut Attributes,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, bool) {
        // [[ attribute-list ]]
        // [[ using attribute-namespace : attribute-list ]]
        //
        // attributes
        //   identifier
        //   attribute-namespace :: identifier
        //   identifier ( argument-list )
        //   attribute-namespace :: identifier ( argument-list )

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::DoubleLeftBrack {
            return (Some(tok), false);
        }

        let up = UsingParser::new(self.lexer);
        let (tok, default_ns) = up.parse();
        let has_using = default_ns.is_some();

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        loop {
            let np = NameParser::new(self.lexer);
            let (tk, (namespace, id)) = np.parse(tok);

            let ap = ArgumentParser::new(self.lexer);
            let (tk, arg) = ap.parse(tk);

            attributes.push(Attribute {
                namespace: namespace.or_else(|| default_ns.clone()),
                name: id,
                arg,
                has_using,
            });

            tok = tk.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => {}
                Token::DoubleRightBrack => {
                    return (None, true);
                }
                _ => {
                    unreachable!("Invalid token in attributes: {:?}", tok);
                }
            }

            tok = self.lexer.next_useful();
        }
    }
}

pub struct AttributesParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> AttributesParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Attributes>) {
        let mut attributes = Vec::new();
        let mut tok = tok;
        let mut has_attributes = false;

        loop {
            let ap = AttributeParser::new(self.lexer);
            let (tk, has_attr) = ap.parse(&mut attributes, tok);
            tok = tk;
            has_attributes |= has_attr;

            if !has_attr {
                break;
            }
        }

        if has_attributes {
            (tok, Some(attributes))
        } else {
            (tok, None)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_attr_single() {
        let mut l = Lexer::<DefaultContext>::new(b"[[noreturn]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: None,
                name: "noreturn".to_string(),
                arg: None,
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_ns() {
        let mut l = Lexer::<DefaultContext>::new(b"[[gnu::unused]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: Some("gnu".to_string()),
                name: "unused".to_string(),
                arg: None,
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_arg() {
        let mut l = Lexer::<DefaultContext>::new(b"[[deprecated(\"because\")]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: None,
                name: "deprecated".to_string(),
                arg: Some(AttributeArg {
                    tokens: vec![Token::LiteralString(b"because"),],
                    buf: Box::new(b"because".to_vec()),
                }),
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_using() {
        let mut l = Lexer::<DefaultContext>::new(b"[[using CC: opt(1), debug]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![
                Attribute {
                    namespace: Some("CC".to_string()),
                    name: "opt".to_string(),
                    arg: Some(AttributeArg {
                        tokens: vec![Token::LiteralInt(1),],
                        buf: Box::new(vec![]),
                    }),
                    has_using: true,
                },
                Attribute {
                    namespace: Some("CC".to_string()),
                    name: "debug".to_string(),
                    arg: None,
                    has_using: true,
                },
            ]
        );
    }

    #[test]
    fn test_attr_several() {
        let mut l = Lexer::<DefaultContext>::new(b"[[A]] [[B]] [[C]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![
                Attribute {
                    namespace: None,
                    name: "A".to_string(),
                    arg: None,
                    has_using: false,
                },
                Attribute {
                    namespace: None,
                    name: "B".to_string(),
                    arg: None,
                    has_using: false,
                },
                Attribute {
                    namespace: None,
                    name: "C".to_string(),
                    arg: None,
                    has_using: false,
                },
            ]
        );
    }
}
