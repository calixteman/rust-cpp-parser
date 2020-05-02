// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::super::r#type::{self, BaseType, CVQualifier, Type};
use super::array::ArrayParser;
use super::function::{ConvOperatorDeclaratorParser, FunctionParser};
use super::pointer::{ParenPointerDeclaratorParser, PointerDeclaratorParser};
use super::r#enum::EnumParser;
use super::specifier::Specifier;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::expression::{ExprNode, ExpressionParser};
use crate::parser::initializer::{Initializer, InitializerParser};
use crate::parser::names::{Qualified, QualifiedParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Identifier {
    pub identifier: Option<Qualified>,
    pub attributes: Option<Attributes>,
}

// TODO: handle structured bindings: https://en.cppreference.com/w/cpp/language/structured_binding
#[derive(Clone, Debug, PartialEq)]
pub struct TypeDeclarator {
    pub typ: Type,
    pub specifier: Specifier,
    pub identifier: Identifier,
    pub init: Option<Initializer>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declaration {
    Type(TypeDeclarator),
    Empty,
}

pub type Declarations = Vec<Declaration>;

impl TypeDeclarator {
    pub(crate) fn is_function(&self) -> bool {
        if let BaseType::Function(_) = self.typ.base {
            true
        } else {
            false
        }
    }

    pub(crate) fn has_semicolon(&self) -> bool {
        if let BaseType::Function(fun) = &self.typ.base {
            fun.body.is_none()
        } else {
            true
        }
    }
}

impl Declaration {
    pub(crate) fn has_semicolon(&self) -> bool {
        true
    }
}

#[derive(Debug)]
pub(crate) enum DeclHint {
    Name(Option<Qualified>),
    Specifier(Specifier),
    Modifier(r#type::Modifier),
    Type(Type),
}

pub struct DeclSpecifierParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclSpecifierParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        hint: Option<DeclHint>,
    ) -> (
        Option<LocToken>,
        (Specifier, Option<Type>, Option<Qualified>),
    ) {
        let (mut typ, mut spec, mut ty_modif) = if let Some(hint) = hint {
            match hint {
                DeclHint::Name(id) => (
                    id.map(BaseType::UD),
                    Specifier::empty(),
                    r#type::Modifier::empty(),
                ),
                DeclHint::Specifier(spec) => (None, spec, r#type::Modifier::empty()),
                DeclHint::Modifier(modif) => (None, Specifier::empty(), modif),
                DeclHint::Type(typ) => {
                    return (tok, (Specifier::empty(), Some(typ), None));
                }
            }
        } else {
            (None, Specifier::empty(), r#type::Modifier::empty())
        };

        let mut cv = CVQualifier::empty();

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        loop {
            // const, volatile
            if cv.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            // typedef, inline, ...
            if spec.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            // unsigned, long, ...
            if ty_modif.from_tok(&tok.tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if ty_modif.is_empty() && typ.is_none() {
                // enum
                let ep = EnumParser::new(self.lexer);
                let (tk, en) = ep.parse(Some(tok));

                if let Some(en) = en {
                    typ = Some(BaseType::Enum(Box::new(en)));
                    tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                    continue;
                }

                // identifier
                let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
                if let Token::Identifier(id) = tk.tok {
                    // TODO: check that the name is a type
                    let qp = QualifiedParser::new(self.lexer);
                    let (tk, name) = qp.parse(None, Some(id));
                    let name = name.unwrap();
                    if name.is_conv_op() {
                        return (tk, (spec, None, Some(name)));
                    }

                    typ = Some(BaseType::UD(name));
                    tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                    continue;
                }

                if tk.tok == Token::Auto {
                    typ = Some(BaseType::Auto);
                    tok = self.lexer.next_useful();
                    continue;
                }

                tok = tk;
            }

            let spec_ty = if let Some(base) = typ {
                (
                    spec,
                    Some(Type {
                        base,
                        cv,
                        pointers: None,
                    }),
                    None,
                )
            } else if cv.is_empty() && ty_modif.is_empty() {
                (spec, None, None)
            } else {
                let typ = if ty_modif.is_empty() {
                    None
                } else {
                    Some(Type {
                        base: BaseType::Primitive(ty_modif.to_primitive()),
                        cv,
                        pointers: None,
                    })
                };

                (spec, typ, None)
            };

            return (Some(tok), spec_ty);
        }
    }
}

pub struct NoPtrDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> NoPtrDeclaratorParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        typ: Type,
        specifier: Specifier,
        is_fun_arg: bool,
    ) -> (Option<LocToken>, Option<TypeDeclarator>) {
        let (tok, identifier) = if !is_fun_arg {
            // declarator-id
            let qp = QualifiedParser::new(self.lexer);
            let (tok, identifier) = qp.parse(tok, None);

            // attributes
            let ap = AttributesParser::new(self.lexer);
            let (tok, attributes) = ap.parse(tok);

            (
                tok,
                Identifier {
                    identifier,
                    attributes,
                },
            )
        } else {
            (
                tok,
                Identifier {
                    identifier: None,
                    attributes: None,
                },
            )
        };

        // function
        let fp = FunctionParser::new(self.lexer);
        let (tok, function) = fp.parse(tok, is_fun_arg);

        if let Some(mut function) = function {
            function.return_type = Some(typ);
            let typ = Type {
                base: BaseType::Function(Box::new(function)),
                cv: CVQualifier::empty(),
                pointers: None,
            };
            return (
                tok,
                Some(TypeDeclarator {
                    typ,
                    specifier,
                    identifier,
                    init: None,
                }),
            );
        }

        // array
        let ap = ArrayParser::new(self.lexer);
        let (tok, array) = ap.parse(tok);

        let typ = if let Some(mut array) = array {
            array.base = Some(typ);
            Type {
                base: BaseType::Array(Box::new(array)),
                cv: CVQualifier::empty(),
                pointers: None,
            }
        } else {
            typ
        };

        // initializer
        let ip = InitializerParser::new(self.lexer);
        let (tok, init) = ip.parse(tok);

        (
            tok,
            Some(TypeDeclarator {
                typ,
                specifier,
                identifier,
                init,
            }),
        )
    }
}

pub struct TypeDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> TypeDeclaratorParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        hint: Option<DeclHint>,
    ) -> (Option<LocToken>, Option<TypeDeclarator>) {
        let dsp = DeclSpecifierParser::new(self.lexer);
        let (tok, (spec, typ, op)) = dsp.parse(tok, hint);

        let typ = if let Some(typ) = typ {
            typ
        } else {
            // conversion operator
            let codp = ConvOperatorDeclaratorParser::new(self.lexer);
            let (tok, conv) = codp.parse(spec, op, tok);

            return (tok, conv);
        };

        let mut typ = typ;

        let ppdp = ParenPointerDeclaratorParser::new(self.lexer);
        let (tok, (paren_decl, is_func_param)) = ppdp.parse(tok);

        let tok = if !is_func_param {
            // Pointer: *, &, &&
            let pdp = PointerDeclaratorParser::new(self.lexer);
            let (tok, ptrs) = pdp.parse(tok, None);

            typ.pointers = ptrs;
            tok
        } else {
            tok
        };

        // int (*f[1]) (int, int) == A *f[1] avec A = int ()(int, int)
        // int (*f[2]) [3] == A * f[2] avec A = int[3]
        // int (*f) (int) == A * f avec A = int () (int)

        let npp = NoPtrDeclaratorParser::new(self.lexer);
        let (tok, decl) = npp.parse(tok, typ, spec, is_func_param);
        let mut decl = decl.unwrap();

        if let Some(paren_decl) = paren_decl {
            let TypeDeclarator {
                typ,
                specifier: _,
                identifier,
                init: _,
            } = paren_decl;
            let Type {
                base,
                cv: _,
                pointers,
            } = typ;

            decl.identifier = identifier;

            match base {
                BaseType::None => {
                    decl.typ.pointers = pointers;
                }
                BaseType::Array(mut array) => {
                    // int (*f[2]) [3] == A * f[2] with A = int[3]
                    // base == BaseType::Array(Array { base: Some(Type { base: None, cv, *}), dim: 2 })
                    // decl.typ.base == BaseType::Array(Array { base: Some(Type { int, cv, }), dim = 3})
                    if let Some(base) = array.base.as_mut() {
                        std::mem::swap(&mut base.base, &mut decl.typ.base);
                    }
                    decl.typ.base = BaseType::Array(array);
                }
                _ => {
                    unreachable!();
                }
            }
        }

        (tok, Some(decl))
    }

    pub(crate) fn is_decl_part(tok: &Token) -> bool {
        match tok {
            Token::Star | Token::And | Token::AndAnd | Token::Identifier(_) => true,
            _ => CVQualifier::is_cv(tok) || Specifier::is_specifier(tok),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclOrExpr {
    Decl(TypeDeclarator),
    Expr(ExprNode),
}

pub(crate) struct DeclOrExprParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclOrExprParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<DeclOrExpr>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok.tok {
            Token::Identifier(id) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, name) = qp.parse(None, Some(id));

                let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                if TypeDeclaratorParser::<PC>::is_decl_part(&tok.tok) {
                    let tp = TypeDeclaratorParser::new(self.lexer);
                    let hint = DeclHint::Name(name);
                    let (tok, typ) = tp.parse(Some(tok), Some(hint));

                    (tok, Some(DeclOrExpr::Decl(typ.unwrap())))
                } else {
                    let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
                    let (tok, expr) = ep.parse_with_id(Some(tok), name.unwrap());

                    (tok, Some(DeclOrExpr::Expr(expr.unwrap())))
                }
            }
            _ => {
                let tp = TypeDeclaratorParser::new(self.lexer);
                let (tok, typ) = tp.parse(Some(tok), None);

                if let Some(typ) = typ {
                    return (tok, Some(DeclOrExpr::Decl(typ)));
                }

                let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
                let (tok, expr) = ep.parse(tok);

                if let Some(expr) = expr {
                    return (tok, Some(DeclOrExpr::Expr(expr)));
                }

                (tok, None)
            }
        }
    }
}

pub struct DeclarationParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        hint: Option<DeclHint>,
    ) -> (Option<LocToken>, Option<Declaration>) {
        let dp = TypeDeclaratorParser::new(self.lexer);
        let (tok, decl) = dp.parse(tok, hint);

        (tok, decl.map(Declaration::Type))
    }
}

#[cfg(test)]
mod tests {

    use super::super::function::*;
    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::array::*;
    use crate::parser::attributes::Attribute;
    use crate::parser::declarations::pointer::*;
    use crate::parser::declarations::r#enum::*;
    use crate::parser::expression::{self, *};
    use crate::parser::literals::{self, *};
    use crate::parser::names::{self, operator, Name};
    use crate::parser::r#type::Primitive;
    use pretty_assertions::assert_eq;

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
            let (_, (_, ty, _)) = p.parse(None, None);

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
            let (_, (_, ty, _)) = p.parse(None, None);
            let ty = &ty.as_ref().unwrap();

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
            let (_, (_, ty, _)) = p.parse(None, None);
            let ty = &ty.as_ref().unwrap();

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
        let mut l = Lexer::<DefaultContext>::new(b"int * x = nullptr");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Pointer,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Equal(ExprNode::Nullptr(Box::new(Nullptr {})))),
            })
        );
    }

    #[test]
    fn test_simple_pointer_ud() {
        let mut l = Lexer::<DefaultContext>::new(b"volatile A::B::C * x = nullptr");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(mk_id!("A", "B", "C")),
                    cv: CVQualifier::VOLATILE,
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Pointer,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Equal(ExprNode::Nullptr(Box::new(Nullptr {})))),
            })
        );
    }

    #[test]
    fn test_list_init() {
        let mut l = Lexer::<DefaultContext>::new(b"const int x{314}");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::CONST,
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Brace(vec![Some(ExprNode::Integer(Box::new(
                    literals::Integer {
                        value: IntLiteral::Int(314)
                    }
                ))),])),
            })
        );
    }

    #[test]
    fn test_simple_const_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"signed short volatile int * const x = NULL");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Short),
                    cv: CVQualifier::VOLATILE,
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Pointer,
                        attributes: None,
                        cv: CVQualifier::CONST,
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Equal(ExprNode::Qualified(Box::new(mk_id!(
                    "NULL"
                ))))),
            })
        );
    }

    #[test]
    fn test_double_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                    ])
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_triple_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** const * x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::CONST,
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                    ])
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_triple_pointer_ud_type() {
        let mut l = Lexer::<DefaultContext>::new(b"A::B ** const * x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(mk_id!("A", "B")),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::CONST,
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                    ])
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_simple_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int & x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Reference,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_simple_rvalue_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int && x");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::RValue,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_simple_rvalue_reference_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"int &&");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::RValue,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: None,
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_double_pointer_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"char **");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Char),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                    ])
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: None,
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_array_ptr() {
        let mut l = Lexer::<DefaultContext>::new(b"int (*foo[2]) [3]");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Array(Box::new(Array {
                        base: Some(Type {
                            base: BaseType::Array(Box::new(Array {
                                base: Some(Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                }),
                                dimensions: vec![Dimension {
                                    size: Some(ExprNode::Integer(Box::new(literals::Integer {
                                        value: IntLiteral::Int(3)
                                    }))),
                                    attributes: None,
                                }],
                            })),
                            cv: CVQualifier::empty(),
                            pointers: Some(vec![Pointer {
                                kind: PtrKind::Pointer,
                                attributes: None,
                                cv: CVQualifier::empty(),
                                ms: MSModifier::empty(),
                            }]),
                        }),
                        dimensions: vec![Dimension {
                            size: Some(ExprNode::Integer(Box::new(literals::Integer {
                                value: IntLiteral::Int(2)
                            }))),
                            attributes: None,
                        }],
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_no_name() {
        let mut l = Lexer::<DefaultContext>::new(b"int *()");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: Some(vec![Pointer {
                                kind: PtrKind::Pointer,
                                attributes: None,
                                cv: CVQualifier::empty(),
                                ms: MSModifier::empty(),
                            }]),
                        }),
                        params: vec![],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: None,
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_1() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("x")),
                                    attributes: None
                                },
                                init: None
                            },
                        }],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_ptr_fun_1() {
        let mut l = Lexer::<DefaultContext>::new(b"int (**) (int x)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("x")),
                                    attributes: None
                                },
                                init: None
                            },
                        }],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: Some(vec![
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        },
                        Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        }
                    ]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: None,
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_1_ptr() {
        let mut l = Lexer::<DefaultContext>::new(b"double ** foo(int x)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Double),
                            cv: CVQualifier::empty(),
                            pointers: Some(vec![
                                Pointer {
                                    kind: PtrKind::Pointer,
                                    attributes: None,
                                    cv: CVQualifier::empty(),
                                    ms: MSModifier::empty(),
                                },
                                Pointer {
                                    kind: PtrKind::Pointer,
                                    attributes: None,
                                    cv: CVQualifier::empty(),
                                    ms: MSModifier::empty(),
                                },
                            ]),
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("x")),
                                    attributes: None
                                },
                                init: None
                            },
                        }],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_2() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo::bar(int x, const double * const y)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![
                            Parameter {
                                attributes: None,
                                decl: TypeDeclarator {
                                    typ: Type {
                                        base: BaseType::Primitive(Primitive::Int),
                                        cv: CVQualifier::empty(),
                                        pointers: None,
                                    },
                                    specifier: Specifier::empty(),
                                    identifier: Identifier {
                                        identifier: Some(mk_id!("x")),
                                        attributes: None
                                    },
                                    init: None
                                },
                            },
                            Parameter {
                                attributes: None,
                                decl: TypeDeclarator {
                                    typ: Type {
                                        base: BaseType::Primitive(Primitive::Double),
                                        cv: CVQualifier::CONST,
                                        pointers: Some(vec![Pointer {
                                            kind: PtrKind::Pointer,
                                            attributes: None,
                                            cv: CVQualifier::CONST,
                                            ms: MSModifier::empty(),
                                        }]),
                                    },
                                    specifier: Specifier::empty(),
                                    identifier: Identifier {
                                        identifier: Some(mk_id!("y")),
                                        attributes: None
                                    },
                                    init: None
                                },
                            }
                        ],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo", "bar")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_1_init() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x = 123)");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("x")),
                                    attributes: None
                                },
                                init: Some(Initializer::Equal(ExprNode::Integer(Box::new(
                                    literals::Integer {
                                        value: IntLiteral::Int(123)
                                    }
                                ))))
                            },
                        }],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_fun_1_init_extra() {
        let mut l = Lexer::<DefaultContext>::new(
            b"int foo([[attribute]] int x = 123) const && throw(A, B) [[noreturn]] -> C",
        );
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: Some(vec![Attribute {
                                namespace: None,
                                name: "attribute".to_string(),
                                arg: None,
                                has_using: false,
                            }]),
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("x")),
                                    attributes: None,
                                },
                                init: Some(Initializer::Equal(ExprNode::Integer(Box::new(
                                    literals::Integer {
                                        value: IntLiteral::Int(123)
                                    }
                                ))))
                            },
                        }],
                        cv: CVQualifier::CONST,
                        refq: RefQualifier::RValue,
                        except: Some(Exception::Throw(Some(vec![
                            Some(ExprNode::Qualified(Box::new(mk_id!("A")))),
                            Some(ExprNode::Qualified(Box::new(mk_id!("B")))),
                        ],))),
                        attributes: Some(vec![Attribute {
                            namespace: None,
                            name: "noreturn".to_string(),
                            arg: None,
                            has_using: false,
                        }]),
                        trailing: Some(ExprNode::Qualified(Box::new(mk_id!("C")))),
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_array() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo[123]");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Array(Box::new(Array {
                        base: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        dimensions: vec![Dimension {
                            size: Some(ExprNode::Integer(Box::new(literals::Integer {
                                value: IntLiteral::Int(123)
                            }))),
                            attributes: None,
                        }],
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_enum() {
        let mut l = Lexer::<DefaultContext>::new(b"typedef enum A { a } B");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Enum(Box::new(Enum {
                        kind: Kind::None,
                        attributes: None,
                        name: Some(mk_id!("A")),
                        base: None,
                        entries: Some(vec![Entry {
                            name: "a".to_string(),
                            attributes: None,
                            init: None
                        },]),
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::TYPEDEF,
                identifier: Identifier {
                    identifier: Some(mk_id!("B")),
                    attributes: None,
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_operator_unary() {
        let mut l = Lexer::<DefaultContext>::new(b"A B::operator+()");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::UD(mk_id!("A")),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(Qualified {
                        names: vec![
                            Name::Identifier(names::Identifier {
                                val: "B".to_string()
                            }),
                            Name::Operator(Box::new(operator::Operator::Op(
                                expression::Operator::Plus
                            ))),
                        ]
                    }),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_operator_conv() {
        let mut l = Lexer::<DefaultContext>::new(b"operator A()");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: None,
                        params: vec![],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(Qualified {
                        names: vec![Name::Operator(Box::new(operator::Operator::Conv(Type {
                            base: BaseType::UD(mk_id!("A")),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },))),]
                    }),
                    attributes: None
                },
                init: None,
            })
        );
    }

    #[test]
    fn test_operator_conv_scoped() {
        let mut l = Lexer::<DefaultContext>::new(b"A::operator B()");
        let p = DeclarationParser::new(&mut l);
        let (_, decl) = p.parse(None, None);
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: None,
                        params: vec![],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(Qualified {
                        names: vec![
                            Name::Identifier(names::Identifier {
                                val: "A".to_string()
                            }),
                            Name::Operator(Box::new(operator::Operator::Conv(Type {
                                base: BaseType::UD(mk_id!("B")),
                                cv: CVQualifier::empty(),
                                pointers: None,
                            },))),
                        ]
                    }),
                    attributes: None
                },
                init: None,
            })
        );
    }
}
