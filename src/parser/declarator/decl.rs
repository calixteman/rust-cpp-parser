use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

use super::specifier::Specifier;

use super::super::r#type::{self, BaseType, CVQualifier, Primitive, Type};

use super::pointer::{Pointer, PointerDeclaratorParser};

use super::reference::{Reference, ReferenceDeclaratorParser};

use super::function::{Parameter, ParameterListParser};

#[derive(Clone, Debug, PartialEq)]
pub enum Declarator {
    Pointer(Pointer),
    Reference(Reference),
    Identifier(String),
    None,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
    pub(crate) ty: Type,
    pub(crate) decl: Declarator,
}

pub struct DeclSpecifierParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    spec: Specifier,
    cv: CVQualifier,
    ty_modif: r#type::Modifier,
}

impl<'a, 'b, PC: PreprocContext> DeclSpecifierParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            spec: Specifier::empty(),
            cv: CVQualifier::empty(),
            ty_modif: r#type::Modifier::empty(),
        }
    }

    pub(super) fn get_type(self) -> Option<Type> {
        if self.spec.is_empty() && self.cv.is_empty() && self.ty_modif.is_empty() {
            None
        } else {
            Some(Type {
                base: BaseType::Primitive(self.ty_modif.to_primitive()),
                cv: self.cv,
            })
        }
    }

    pub(super) fn parse(
        mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Type>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        loop {
            if self.cv.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if self.spec.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if self.ty_modif.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            return (Some(tok), self.get_type());
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

    pub(super) fn parse(self, tok: LocToken<'a>) -> (Option<LocToken<'a>>, Option<Declarator>) {
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
            Token::Identifier(id) => {
                let id = id.to_string();
                let mut plp = ParameterListParser::new(self.lexer);
                let (tok, params) = plp.parse(None);
                if let Some(params) = params {}

                let tok = self.lexer.next_useful();
                match tok.tok {
                    Token::LeftParen => {
                        let mut plp = ParameterListParser::new(self.lexer);
                        let (tok, params) = plp.parse(None);
                    }
                    Token::LeftBrack => {}
                    _ => {}
                }

                return (None, Some(Declarator::Identifier(id.to_string())));
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
            let (tok, decl) = dp.parse(tok.unwrap());
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

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;

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
                    decl: Box::new(Declarator::Identifier("x".to_string())),
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
                    decl: Box::new(Declarator::Identifier("x".to_string())),
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
                        decl: Box::new(Declarator::Identifier("x".to_string())),
                        cv: CVQualifier::empty(),
                    })),
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
                            decl: Box::new(Declarator::Identifier("x".to_string())),
                            cv: CVQualifier::empty(),
                        })),
                        cv: CVQualifier::empty(),
                    })),
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
                            decl: Box::new(Declarator::Identifier("x".to_string())),
                            cv: CVQualifier::empty(),
                        })),
                        cv: CVQualifier::CONST,
                    })),
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
                    decl: Box::new(Declarator::Identifier("x".to_string())),
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
                    decl: Box::new(Declarator::Identifier("x".to_string())),
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
                        cv: CVQualifier::empty(),
                    })),
                    cv: CVQualifier::empty(),
                })
            }
        );
    }
}
