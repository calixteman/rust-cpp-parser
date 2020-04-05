use super::super::r#type::{self, BaseType, CVQualifier, Primitive, Type};
use super::array::{Array, ArrayParser};
use super::function::{Function, FunctionParser};
use super::pointer::{Pointer, PointerDeclaratorParser};
use super::reference::{Reference, ReferenceDeclaratorParser};
use super::specifier::Specifier;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::name::{Qualified, QualifiedParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Identifier {
    pub(crate) identifier: Qualified,
    pub(crate) attributes: Option<Attributes>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declarator {
    Pointer(Pointer),
    Reference(Reference),
    Identifier(Identifier),
    Function(Function),
    Array(Array),
    None,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub(crate) ty: Type,
    pub(crate) decl: Declarator,
}

pub struct DeclSpecifierParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclSpecifierParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken<'a>>) -> (Option<LocToken<'a>>, Option<Type>) {
        let mut spec = Specifier::empty();
        let mut cv = CVQualifier::empty();
        let mut ty_modif = r#type::Modifier::empty();

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        loop {
            if cv.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if spec.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if ty_modif.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            let ty = if spec.is_empty() && cv.is_empty() && ty_modif.is_empty() {
                None
            } else {
                Some(Type {
                    base: BaseType::Primitive(ty_modif.to_primitive()),
                    cv,
                })
            };

            return (Some(tok), ty);
        }
    }
}

pub struct DeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Declarator>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok.tok {
            Token::Star => {
                let pdp = PointerDeclaratorParser::new(self.lexer);
                let (tok, decl) = pdp.parse();

                return (tok, Some(Declarator::Pointer(decl)));
            }
            Token::And => {
                let rdp = ReferenceDeclaratorParser::new(self.lexer, true /* lvalue */);
                let (tok, decl) = rdp.parse();

                return (tok, Some(Declarator::Reference(decl)));
            }
            Token::AndAnd => {
                let rdp = ReferenceDeclaratorParser::new(self.lexer, false /* lvalue */);
                let (tok, decl) = rdp.parse();

                return (tok, Some(Declarator::Reference(decl)));
            }
            Token::Identifier(_) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, qual) = qp.parse(Some(tok));

                let ap = AttributesParser::new(self.lexer);
                let (tok, attributes) = ap.parse(tok);

                let fp = FunctionParser::new(self.lexer);
                let (tok, function) = fp.parse(tok);

                if let Some(mut function) = function {
                    function.identifier = qual;
                    function.id_attributes = attributes;
                    return (tok, Some(Declarator::Function(function)));
                }

                let ap = ArrayParser::new(self.lexer);
                let (tok, array) = ap.parse(tok);

                if let Some(mut array) = array {
                    array.identifier = qual;
                    array.id_attributes = attributes;
                    return (tok, Some(Declarator::Array(array)));
                }

                return (
                    tok,
                    Some(Declarator::Identifier(Identifier {
                        identifier: qual.unwrap(),
                        attributes,
                    })),
                );
            }
            _ => {
                return (Some(tok), Some(Declarator::None));
            }
        }
    }
}

pub struct DeclarationParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Declaration>) {
        let dsp = DeclSpecifierParser::new(self.lexer);
        let (tok, ty) = dsp.parse(tok);

        if let Some(ty) = ty {
            let dp = DeclaratorParser::new(self.lexer);
            let (tok, decl) = dp.parse(tok);
            if let Some(decl) = decl {
                return (tok, Some(Declaration { ty, decl }));
            } else {
                unreachable!();
            }
        } else {
            return (tok, None);
        }
    }
}

#[cfg(test)]
mod tests {

    use super::super::function::*;
    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::attributes::Attribute;
    use crate::parser::expression::*;
    use crate::parser::name::Name;
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_primitive() {
        for (buf, res) in vec![
            ("void", Primitive::Void),
            ("char", Primitive::Char),
            ("signed char", Primitive::SignedChar),
            ("unsigned char", Primitive::UnsignedChar),
            ("short", Primitive::Short),
            ("short int", Primitive::Short),
            ("signed short", Primitive::Short),
            ("signed short int", Primitive::Short),
            ("unsigned short", Primitive::UnsignedShort),
            ("unsigned short int", Primitive::UnsignedShort),
            ("signed", Primitive::Int),
            ("signed int", Primitive::Int),
            ("int", Primitive::Int),
            ("unsigned", Primitive::UnsignedInt),
            ("unsigned int", Primitive::UnsignedInt),
            ("float", Primitive::Float),
            ("double", Primitive::Double),
            ("long double", Primitive::LongDouble),
            ("bool", Primitive::Bool),
            ("wchar_t", Primitive::WcharT),
            ("char8_t", Primitive::Char8T),
            ("char16_t", Primitive::Char16T),
            ("char32_t", Primitive::Char32T),
            ("float _Complex", Primitive::FloatComplex),
            ("double _Complex", Primitive::DoubleComplex),
            ("long double _Complex", Primitive::LongDoubleComplex),
            ("float _Imaginary", Primitive::FloatImaginary),
            ("double _Imaginary", Primitive::DoubleImaginary),
            ("long double _Imaginary", Primitive::LongDoubleImaginary),
        ] {
            let mut l = Lexer::<DefaultContext>::new(buf.as_bytes());
            let p = DeclSpecifierParser::new(&mut l);
            let (_, ty) = p.parse(None);

            let ty = match ty.as_ref().unwrap().base() {
                BaseType::Primitive(ty) => ty,
                _ => unreachable!(),
            };

            assert_eq!(*ty, res, "{}", buf);
        }
    }

    #[test]
    fn test_const_primitive() {
        for (buf, res) in vec![
            ("const short", Primitive::Short),
            ("short const", Primitive::Short),
            ("short const int", Primitive::Short),
            ("signed short const", Primitive::Short),
            ("signed short const int", Primitive::Short),
        ] {
            let mut l = Lexer::<DefaultContext>::new(buf.as_bytes());
            let p = DeclSpecifierParser::new(&mut l);
            let (_, ty) = p.parse(None);
            let ty = ty.as_ref().unwrap();

            assert!(ty.is_const(), "{}", buf);

            let ty = match ty.base() {
                BaseType::Primitive(ty) => ty,
                _ => unreachable!(),
            };

            assert_eq!(*ty, res, "{}", buf);
        }
    }

    #[test]
    fn test_volatile_primitive() {
        for (buf, res) in vec![
            ("volatile short", Primitive::Short),
            ("short volatile", Primitive::Short),
            ("short volatile int", Primitive::Short),
            ("signed short volatile", Primitive::Short),
            ("signed short volatile int", Primitive::Short),
        ] {
            let mut l = Lexer::<DefaultContext>::new(buf.as_bytes());
            let p = DeclSpecifierParser::new(&mut l);
            let (_, ty) = p.parse(None);
            let ty = ty.as_ref().unwrap();

            assert!(ty.is_volatile(), "{}", buf);

            let ty = match ty.base() {
                BaseType::Primitive(ty) => ty,
                _ => unreachable!(),
            };

            assert_eq!(*ty, res, "{}", buf);
        }
    }

    #[test]
    fn test_simple_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"int * x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Identifier(Identifier {
                        identifier: mk_id!("x"),
                        attributes: None,
                    })),
                    attributes: None,
                    cv: CVQualifier::empty(),
                })
            }
        );
    }

    #[test]
    fn test_simple_const_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"signed short volatile int * const x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Short),
                    cv: CVQualifier::VOLATILE,
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Identifier(Identifier {
                        identifier: mk_id!("x"),
                        attributes: None,
                    })),
                    attributes: None,
                    cv: CVQualifier::CONST,
                })
            }
        );
    }

    #[test]
    fn test_double_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Pointer(Pointer {
                        decl: Box::new(Declarator::Identifier(Identifier {
                            identifier: mk_id!("x"),
                            attributes: None,
                        })),
                        attributes: None,
                        cv: CVQualifier::empty(),
                    })),
                    attributes: None,
                    cv: CVQualifier::empty(),
                })
            }
        );
    }

    #[test]
    fn test_triple_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char *** x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Pointer(Pointer {
                        decl: Box::new(Declarator::Pointer(Pointer {
                            decl: Box::new(Declarator::Identifier(Identifier {
                                identifier: mk_id!("x"),
                                attributes: None,
                            })),
                            attributes: None,
                            cv: CVQualifier::empty(),
                        })),
                        attributes: None,
                        cv: CVQualifier::empty(),
                    })),
                    attributes: None,
                    cv: CVQualifier::empty(),
                })
            }
        );
    }

    #[test]
    fn test_triple_constpointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** const * x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Pointer(Pointer {
                        decl: Box::new(Declarator::Pointer(Pointer {
                            decl: Box::new(Declarator::Identifier(Identifier {
                                identifier: mk_id!("x"),
                                attributes: None,
                            })),
                            attributes: None,
                            cv: CVQualifier::empty(),
                        })),
                        attributes: None,
                        cv: CVQualifier::CONST,
                    })),
                    attributes: None,
                    cv: CVQualifier::empty(),
                })
            }
        );
    }

    #[test]
    fn test_simple_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int & x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Reference(Reference {
                    decl: Box::new(Declarator::Identifier(Identifier {
                        identifier: mk_id!("x"),
                        attributes: None,
                    })),
                    attributes: None,
                    lvalue: true,
                })
            }
        );
    }

    #[test]
    fn test_simple_rvalue_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int && x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Reference(Reference {
                    decl: Box::new(Declarator::Identifier(Identifier {
                        identifier: mk_id!("x"),
                        attributes: None,
                    })),
                    attributes: None,
                    lvalue: false,
                })
            }
        );
    }

    #[test]
    fn test_simple_rvalue_reference_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"int &&");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Reference(Reference {
                    decl: Box::new(Declarator::None),
                    attributes: None,
                    lvalue: false,
                })
            }
        );
    }

    #[test]
    fn test_double_pointer_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"char **");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Pointer(Pointer {
                    decl: Box::new(Declarator::Pointer(Pointer {
                        decl: Box::new(Declarator::None),
                        attributes: None,
                        cv: CVQualifier::empty(),
                    })),
                    attributes: None,
                    cv: CVQualifier::empty(),
                })
            }
        );
    }

    #[test]
    fn test_fun_1() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Function(Function {
                    identifier: Some(mk_id!("foo")),
                    id_attributes: None,
                    params: vec![Parameter::Single(Single {
                        attributes: None,
                        ty: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                        },
                        decl: Declarator::Identifier(Identifier {
                            identifier: mk_id!("x"),
                            attributes: None,
                        }),
                    })],
                    cv: CVQualifier::empty(),
                    refq: RefQualifier::None,
                    except: None,
                    attributes: None,
                    trailing: None,
                }),
            }
        );
    }

    #[test]
    fn test_fun_2() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo::bar(int x, const double * const y)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Function(Function {
                    identifier: Some(mk_id!("foo", "bar")),
                    id_attributes: None,
                    params: vec![
                        Parameter::Single(Single {
                            attributes: None,
                            ty: Type {
                                base: BaseType::Primitive(Primitive::Int),
                                cv: CVQualifier::empty(),
                            },
                            decl: Declarator::Identifier(Identifier {
                                identifier: mk_id!("x"),
                                attributes: None,
                            }),
                        }),
                        Parameter::Single(Single {
                            attributes: None,
                            ty: Type {
                                base: BaseType::Primitive(Primitive::Double),
                                cv: CVQualifier::CONST,
                            },
                            decl: Declarator::Pointer(Pointer {
                                decl: Box::new(Declarator::Identifier(Identifier {
                                    identifier: mk_id!("y"),
                                    attributes: None,
                                })),
                                attributes: None,
                                cv: CVQualifier::CONST,
                            }),
                        })
                    ],
                    cv: CVQualifier::empty(),
                    refq: RefQualifier::None,
                    except: None,
                    attributes: None,
                    trailing: None,
                }),
            }
        );
    }

    #[test]
    fn test_fun_1_init() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x = 123)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Function(Function {
                    identifier: Some(mk_id!("foo")),
                    id_attributes: None,
                    params: vec![Parameter::Init(Init {
                        attributes: None,
                        ty: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                        },
                        decl: Declarator::Identifier(Identifier {
                            identifier: mk_id!("x"),
                            attributes: None,
                        }),
                        init: Node::UInt(Box::new(UInt { value: 123 })),
                    })],
                    cv: CVQualifier::empty(),
                    refq: RefQualifier::None,
                    except: None,
                    attributes: None,
                    trailing: None,
                }),
            }
        );
    }

    #[test]
    fn test_fun_1_init_extra() {
        let mut l = Lexer::<DefaultContext>::new(
            b"int foo([[attribute]] int x = 123) const && throw(A, B) [[noreturn]] -> C",
        );
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Function(Function {
                    identifier: Some(mk_id!("foo")),
                    id_attributes: None,
                    params: vec![Parameter::Init(Init {
                        attributes: Some(vec![Attribute {
                            namespace: None,
                            name: "attribute".to_string(),
                            arg: None,
                            has_using: false,
                        }]),
                        ty: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                        },
                        decl: Declarator::Identifier(Identifier {
                            identifier: mk_id!("x"),
                            attributes: None,
                        }),
                        init: Node::UInt(Box::new(UInt { value: 123 })),
                    })],
                    cv: CVQualifier::CONST,
                    refq: RefQualifier::RValue,
                    except: Some(Exception::Throw(Some(vec![
                        Some(Node::Qualified(Box::new(mk_id!("A")))),
                        Some(Node::Qualified(Box::new(mk_id!("B")))),
                    ],))),
                    attributes: Some(vec![Attribute {
                        namespace: None,
                        name: "noreturn".to_string(),
                        arg: None,
                        has_using: false,
                    }]),
                    trailing: Some(Node::Qualified(Box::new(mk_id!("C")))),
                }),
            }
        );
    }

    #[test]
    fn test_array() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo[123]");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration {
                ty: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                },
                decl: Declarator::Array(Array {
                    identifier: Some(mk_id!("foo")),
                    id_attributes: None,
                    size: Some(Node::UInt(Box::new(UInt { value: 123 }))),
                    attributes: None,
                }),
            }
        );
    }
}
