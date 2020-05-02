use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::declarations::DeclSpecifierParser;
use crate::parser::expression::{ExprNode, ExpressionParser};
use crate::parser::names::{Qualified, QualifiedParser};
use crate::parser::r#type::Type;

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Struct,
    Class,
    None,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Entry {
    pub(crate) name: String,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) init: Option<ExprNode>,
}

pub type Entries = Vec<Entry>;

#[derive(Clone, Debug, PartialEq)]
pub struct Enum {
    pub(crate) kind: Kind,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) name: Option<Qualified>,
    pub(crate) base: Option<Type>,
    pub(crate) entries: Option<Entries>,
}

struct BaseTypeParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> BaseTypeParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Type>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok.tok != Token::Colon {
            return (Some(tok), None);
        }

        let dsp = DeclSpecifierParser::new(self.lexer);
        let (tok, (_, ty, _)) = dsp.parse(None, None);

        (tok, ty)
    }
}

struct EntryParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> EntryParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Entry>) {
        // Identifier
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, id) = if let Token::Identifier(id) = tok.tok {
            (None, id)
        } else {
            return (Some(tok), None);
        };

        // optional: attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, init) = if tok.tok == Token::Equal {
            let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
            ep.parse(None)
        } else {
            (Some(tok), None)
        };

        (
            tok,
            Some(Entry {
                name: id,
                attributes,
                init,
            }),
        )
    }
}

struct EntriesParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> EntriesParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Entries>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftBrace {
            return (Some(tok), None);
        }

        let mut entries = Vec::new();

        loop {
            let ep = EntryParser::new(self.lexer);
            let (tok, entry) = ep.parse(None);

            if let Some(entry) = entry {
                entries.push(entry);
            }

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => continue,
                Token::RightBrace => {
                    return (None, Some(entries));
                }
                _ => unreachable!("Invalid token in enum definition: {:?}", tok),
            }
        }
    }
}

pub(crate) struct EnumParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> EnumParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Enum>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok.tok != Token::Enum {
            return (Some(tok), None);
        }

        // enum, enum struct, enum class
        let tok = self.lexer.next_useful();
        let (kind, tok) = match tok.tok {
            Token::Struct => (Kind::Struct, self.lexer.next_useful()),
            Token::Class => (Kind::Class, self.lexer.next_useful()),
            _ => (Kind::None, tok),
        };

        // optional: attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(Some(tok));

        // optional: name
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(tok, None);

        // optional: ':' base-type
        let btp = BaseTypeParser::new(self.lexer);
        let (tok, base) = btp.parse(tok);

        // optional: '{' ... '}'
        let ep = EntriesParser::new(self.lexer);
        let (tok, entries) = ep.parse(tok);

        (
            tok,
            Some(Enum {
                kind,
                attributes,
                name,
                base,
                entries,
            }),
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::attributes::*;
    use crate::parser::expression::*;
    use crate::parser::literals::*;
    use crate::parser::names::*;
    use crate::parser::r#type::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_enum_basic() {
        let mut l = Lexer::<DefaultContext>::new(b"enum Color {red, green , blue}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::None,
                attributes: None,
                name: Some(mk_id!("Color")),
                base: None,
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: None
                    },
                ]),
            }
        );
    }

    #[test]
    fn test_enum_no_name() {
        let mut l = Lexer::<DefaultContext>::new(b"enum {red, green , blue}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::None,
                attributes: None,
                name: None,
                base: None,
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: None
                    },
                ]),
            }
        );
    }

    #[test]
    fn test_enum_base() {
        let mut l =
            Lexer::<DefaultContext>::new(b"enum Color : unsigned short {red, green , blue}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::None,
                attributes: None,
                name: Some(mk_id!("Color")),
                base: Some(Type {
                    base: BaseType::Primitive(Primitive::UnsignedShort),
                    cv: CVQualifier::empty(),
                    pointers: None,
                }),
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: None
                    },
                ]),
            }
        );
    }

    #[test]
    fn test_enum_base_no_body() {
        let mut l = Lexer::<DefaultContext>::new(b"enum Color : unsigned short");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::None,
                attributes: None,
                name: Some(mk_id!("Color")),
                base: Some(Type {
                    base: BaseType::Primitive(Primitive::UnsignedShort),
                    cv: CVQualifier::empty(),
                    pointers: None,
                }),
                entries: None,
            }
        );
    }

    #[test]
    fn test_enum_base_init() {
        let mut l = Lexer::<DefaultContext>::new(
            b"enum Color : unsigned short {red = 0, green [[attr]] = 2, blue = 0xFF00}}",
        );
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::None,
                attributes: None,
                name: Some(mk_id!("Color")),
                base: Some(Type {
                    base: BaseType::Primitive(Primitive::UnsignedShort),
                    cv: CVQualifier::empty(),
                    pointers: None,
                }),
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: Some(ExprNode::Integer(Box::new(Integer {
                            value: IntLiteral::Int(0)
                        })))
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: Some(vec![Attribute {
                            namespace: None,
                            name: "attr".to_string(),
                            arg: None,
                            has_using: false,
                        }]),
                        init: Some(ExprNode::Integer(Box::new(Integer {
                            value: IntLiteral::Int(2)
                        })))
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: Some(ExprNode::Integer(Box::new(Integer {
                            value: IntLiteral::Int(0xFF00)
                        })))
                    },
                ],),
            }
        );
    }

    #[test]
    fn test_enum_class() {
        let mut l = Lexer::<DefaultContext>::new(b"enum class Color {red, green , blue}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::Class,
                attributes: None,
                name: Some(mk_id!("Color")),
                base: None,
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: None
                    },
                ]),
            }
        );
    }

    #[test]
    fn test_enum_struct() {
        let mut l =
            Lexer::<DefaultContext>::new(b"enum struct [[attr]] Color: char {red, green , blue}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::Struct,
                attributes: Some(vec![Attribute {
                    namespace: None,
                    name: "attr".to_string(),
                    arg: None,
                    has_using: false,
                }]),
                name: Some(mk_id!("Color")),
                base: Some(Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                    pointers: None,
                }),
                entries: Some(vec![
                    Entry {
                        name: "red".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "green".to_string(),
                        attributes: None,
                        init: None
                    },
                    Entry {
                        name: "blue".to_string(),
                        attributes: None,
                        init: None
                    },
                ]),
            }
        );
    }

    #[test]
    fn test_enum_class_no_entries() {
        let mut l = Lexer::<DefaultContext>::new(b"enum class byte : unsigned char {}");
        let p = EnumParser::new(&mut l);
        let (_, e) = p.parse(None);

        assert_eq!(
            e.unwrap(),
            Enum {
                kind: Kind::Class,
                attributes: None,
                name: Some(mk_id!("byte")),
                base: Some(Type {
                    base: BaseType::Primitive(Primitive::UnsignedChar),
                    cv: CVQualifier::empty(),
                    pointers: None,
                }),
                entries: Some(vec![])
            }
        );
    }
}
