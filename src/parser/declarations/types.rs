// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::array::ArrayParser;
use super::class::ClassParser;
use super::function::{ConvOperatorDeclaratorParser, FunctionParser};
use super::pointer::{ParenPointerDeclaratorParser, PointerDeclaratorParser};
use super::r#enum::EnumParser;
use super::specifier::Specifier;
use crate::lexer::{
    extra::{CombinedLexers, SavedLexer},
    TLexer, Token,
};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::context::{Context, SearchResult, TypeToFix};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{ExprNode, ExpressionParser, VarDecl, Variable};
use crate::parser::initializer::{Initializer, InitializerParser};
use crate::parser::names::{Qualified, QualifiedParser};
use crate::parser::types::{self, BaseType, CVQualifier, Modifier, Type, UDType, UserDefined};

#[derive(Clone, Debug, PartialEq)]
pub struct Identifier {
    pub identifier: Option<Qualified>,
    pub attributes: Option<Attributes>,
}

impl Dump for Identifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, identifier, attributes);
    }
}

// TODO: handle structured bindings: https://en.cppreference.com/w/cpp/language/structured_binding
#[derive(Clone, Debug, PartialEq)]
pub struct TypeDeclarator {
    pub typ: Type,
    pub specifier: Specifier,
    pub identifier: Identifier,
    pub init: Option<Initializer>,
    pub bitfield_size: Option<ExprNode>,
}

impl Dump for TypeDeclarator {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "type-decl",
            prefix,
            last,
            stdout,
            typ,
            specifier,
            identifier,
            init,
            bitfield_size
        );
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct TypeDeclNames<'a> {
    pub(crate) var: Option<&'a Qualified>,
    pub(crate) typ: Option<&'a Qualified>,
    pub(crate) typd: Option<&'a Qualified>,
}

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

    pub(crate) fn is_type_part(tok: &Token) -> bool {
        *tok == Token::Class || *tok == Token::Enum || *tok == Token::Struct
    }

    pub fn is_type(&self) -> bool {
        if self.specifier.intersects(Specifier::TYPEDEF) {
            true
        } else {
            /*match self.typ.base {

            }*/
            false
        }
    }

    pub(crate) fn get_names(&self) -> TypeDeclNames {
        // Get the variable names (if any) and the type name (if any)
        // var and typd are exclusive
        // but we can have a typd and typ, e.g. typedef class A {...} B;
        let (var, typd) = if self.specifier.intersects(Specifier::TYPEDEF) {
            (None, self.identifier.identifier.as_ref())
        } else {
            (self.identifier.identifier.as_ref(), None)
        };

        let typ = match &self.typ.base {
            BaseType::Class(c) => c.name.as_ref(),
            BaseType::Enum(e) => e.name.as_ref(),
            _ => None,
        };

        TypeDeclNames { var, typ, typd }
    }

    pub(crate) fn get_repr(&self) -> Option<String> {
        match &self.typ.base {
            BaseType::Class(_) => Some("class".to_string()),
            BaseType::Enum(_) => Some("enum".to_string()),
            BaseType::Function(_) => Some("function".to_string()),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub(crate) enum DeclHint {
    Name(Option<Qualified>),
    Specifier(Specifier),
    Modifier(types::Modifier),
    Type(BaseType),
}

pub struct DeclSpecifierParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> DeclSpecifierParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        hint: Option<DeclHint>,
        context: &mut Context,
    ) -> Result<
        (
            Option<Token>,
            (
                Specifier,
                Option<Type>,
                Option<Qualified>,
                Option<TypeToFix>,
            ),
        ),
        ParserError,
    > {
        let (mut typ, mut spec, mut ty_modif) = if let Some(hint) = hint {
            match hint {
                DeclHint::Name(id) => (
                    id.map(|id| {
                        BaseType::UD(Box::new(UserDefined {
                            name: id,
                            typ: UDType::Indirect(TypeToFix::default()),
                        }))
                    }),
                    Specifier::empty(),
                    types::Modifier::empty(),
                ),
                DeclHint::Specifier(spec) => (None, spec, types::Modifier::empty()),
                DeclHint::Modifier(modif) => (None, Specifier::empty(), modif),
                DeclHint::Type(typ) => (Some(typ), Specifier::empty(), types::Modifier::empty()),
            }
        } else {
            (None, Specifier::empty(), types::Modifier::empty())
        };

        let mut cv = CVQualifier::empty();
        let mut to_fix = None;

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        loop {
            // const, volatile
            if cv.from_tok(&tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            // typedef, inline, ...
            if spec.from_tok(&tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            // unsigned, long, ...
            if ty_modif.from_tok(&tok) {
                tok = self.lexer.next_useful();
                continue;
            }

            if ty_modif.is_empty() && typ.is_none() {
                // enum
                let ep = EnumParser::new(self.lexer);
                let (tk, en, tf) = ep.parse(Some(tok), context)?;

                if let Some(en) = en {
                    typ = Some(BaseType::Enum(Box::new(en)));
                    tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                    to_fix = tf;
                    continue;
                }

                // class
                let cp = ClassParser::new(self.lexer);
                let (tk, cl, tf) = cp.parse(tk, context)?;

                if let Some(cl) = cl {
                    typ = Some(BaseType::Class(Box::new(cl)));
                    tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                    to_fix = tf;
                    continue;
                }

                // identifier
                let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
                if let Token::Identifier(id) = tk {
                    let qp = QualifiedParser::new(self.lexer);
                    let (tk, name) = qp.parse(None, Some(id), context)?;
                    let name = name.unwrap();
                    if name.is_conv_op() {
                        return Ok((tk, (spec, None, Some(name), to_fix)));
                    }

                    let ud_typ = if let Some(res) = context.search(Some(&name)) {
                        match res {
                            SearchResult::Type(ty) => UDType::Direct(ty),
                            SearchResult::Var(_) | SearchResult::IncompleteVar(_) => {
                                return Err(ParserError::InvalidVarInDecl {
                                    sp: self.lexer.span(),
                                    name: name.to_string(),
                                });
                            }
                            SearchResult::IncompleteType(ty) => UDType::Indirect(ty),
                        }
                    } else {
                        UDType::Indirect(TypeToFix::default())
                    };

                    typ = Some(BaseType::UD(Box::new(UserDefined { name, typ: ud_typ })));
                    tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                    continue;
                }

                if tk == Token::Auto {
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
                    to_fix,
                )
            } else if cv.is_empty() && ty_modif.is_empty() {
                (spec, None, None, to_fix)
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

                (spec, typ, None, to_fix)
            };

            return Ok((Some(tok), spec_ty));
        }
    }
}

pub struct NoPtrDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> NoPtrDeclaratorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        typ: Type,
        specifier: Specifier,
        is_fun_arg: bool,
        init: bool,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<TypeDeclarator>, Option<TypeToFix>), ParserError> {
        let (tok, identifier) = if !is_fun_arg {
            // declarator-id
            let qp = QualifiedParser::new(self.lexer);
            let (tok, identifier) = qp.parse(tok, None, context)?;

            // attributes
            let ap = AttributesParser::new(self.lexer);
            let (tok, attributes) = ap.parse(tok, context)?;

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
        let (tok, function, to_fix) =
            fp.parse(tok, is_fun_arg, identifier.identifier.as_ref(), context)?;

        if let Some(mut function) = function {
            function.return_type = Some(typ);
            let typ = Type {
                base: BaseType::Function(Box::new(function)),
                cv: CVQualifier::empty(),
                pointers: None,
            };
            return Ok((
                tok,
                Some(TypeDeclarator {
                    typ,
                    specifier,
                    identifier,
                    init: None,
                    bitfield_size: None,
                }),
                to_fix,
            ));
        }

        // array
        let ap = ArrayParser::new(self.lexer);
        let (tok, array) = ap.parse(tok, context)?;

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
        let (tok, init) = if init {
            let ip = InitializerParser::new(self.lexer);
            ip.parse(tok, context)?
        } else {
            (tok, None)
        };

        Ok((
            tok,
            Some(TypeDeclarator {
                typ,
                specifier,
                identifier,
                init,
                bitfield_size: None,
            }),
            None,
        ))
    }
}

pub struct TypeDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> TypeDeclaratorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        hint: Option<DeclHint>,
        init: bool,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Rc<TypeDeclarator>>), ParserError> {
        let dsp = DeclSpecifierParser::new(self.lexer);
        let (tok, (spec, typ, op, to_fix)) = dsp.parse(tok, hint, context)?;

        let typ = if let Some(typ) = typ {
            typ
        } else {
            // conversion operator
            let codp = ConvOperatorDeclaratorParser::new(self.lexer);
            let (tok, conv, to_fix) = codp.parse(spec, op, tok, context)?;
            let conv = if let Some(conv) = conv {
                let conv = Rc::new(conv);
                if let Some(to_fix) = to_fix {
                    to_fix.fix(Rc::clone(&conv));
                }
                Some(conv)
            } else {
                None
            };

            return Ok((tok, conv));
        };

        let mut typ = typ;

        let ppdp = ParenPointerDeclaratorParser::new(self.lexer);
        let (tok, (paren_decl, is_func_param)) = ppdp.parse(tok, context)?;

        let tok = if !is_func_param {
            // Pointer: *, &, &&
            let pdp = PointerDeclaratorParser::new(self.lexer);
            let (tok, ptrs) = pdp.parse(tok, None, context)?;

            typ.pointers = ptrs;
            tok
        } else {
            tok
        };

        // int (*f[1]) (int, int) == A *f[1] avec A = int ()(int, int)
        // int (*f[2]) [3] == A * f[2] avec A = int[3]
        // int (*f) (int) == A * f avec A = int () (int)

        let npdp = NoPtrDeclaratorParser::new(self.lexer);
        let (tok, decl, tf) = npdp.parse(tok, typ, spec, is_func_param, init, context)?;
        let mut decl = decl.unwrap();
        let to_fix = if to_fix.is_none() { tf } else { to_fix };

        if let Some(paren_decl) = paren_decl {
            let TypeDeclarator {
                typ,
                specifier: _,
                identifier,
                init: _,
                bitfield_size: _,
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

        let decl = Rc::new(decl);
        if let Some(to_fix) = to_fix {
            to_fix.fix(Rc::clone(&decl));
        }

        Ok((tok, Some(decl)))
    }

    pub(crate) fn is_decl_part(tok: &Token) -> bool {
        match tok {
            Token::Star | Token::And | Token::AndAnd => true,
            _ => CVQualifier::is_cv(tok) || Specifier::is_specifier(tok),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclOrExpr {
    Decl(Rc<TypeDeclarator>),
    Expr(ExprNode),
}

impl Dump for DeclOrExpr {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        match self {
            Self::Decl(x) => {
                let prefix = dump_start!(name, "decl-or-expr", prefix, last, stdout);
                x.dump("decl", &prefix, true, stdout);
            }
            Self::Expr(x) => {
                let prefix = dump_start!(name, "", prefix, last, stdout);
                x.dump("expr", &prefix, true, stdout);
            }
        }
    }
}

pub(crate) struct DeclOrExprParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> DeclOrExprParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<DeclOrExpr>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (typ, var, tok) = match tok {
            Token::Identifier(id) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, name) = qp.parse(None, Some(id), context)?;

                if let Some(res) = context.search(name.as_ref()) {
                    match res {
                        SearchResult::Var(var) => (
                            None,
                            Some(ExprNode::Variable(Box::new(Variable {
                                name: name.unwrap(),
                                decl: VarDecl::Direct(var),
                            }))),
                            tok,
                        ),
                        SearchResult::IncompleteVar(var) => (
                            None,
                            Some(ExprNode::Variable(Box::new(Variable {
                                name: name.unwrap(),
                                decl: VarDecl::Indirect(var),
                            }))),
                            tok,
                        ),
                        SearchResult::Type(typ) => (
                            Some(BaseType::UD(Box::new(UserDefined {
                                name: name.unwrap(),
                                typ: UDType::Direct(typ),
                            }))),
                            None,
                            tok,
                        ),
                        SearchResult::IncompleteType(typ) => (
                            Some(BaseType::UD(Box::new(UserDefined {
                                name: name.unwrap(),
                                typ: UDType::Indirect(typ),
                            }))),
                            None,
                            tok,
                        ),
                    }
                } else {
                    return Err(ParserError::UnknownId {
                        sp: self.lexer.span(),
                        name: name.unwrap().to_string(),
                    });
                }
            }
            _ => {
                if Modifier::is_primitive_part(&tok) {
                    let mut modif = Modifier::empty();
                    modif.from_tok(&tok);

                    let tok = self.lexer.next_useful();
                    if tok == Token::LeftParen {
                        (
                            Some(BaseType::Primitive(modif.to_primitive())),
                            None,
                            Some(tok),
                        )
                    } else {
                        let tdp = TypeDeclaratorParser::new(self.lexer);
                        let (tok, typ) =
                            tdp.parse(Some(tok), Some(DeclHint::Modifier(modif)), true, context)?;

                        return Ok((tok, Some(DeclOrExpr::Decl(typ.unwrap()))));
                    }
                } else {
                    (None, None, Some(tok))
                }
            }
        };

        if let Some(typ) = typ {
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok == Token::LeftParen {
                // We can't know what we have here until we know the token just after
                // the closing parenthesis, so perform a lookahead.
                let (tok, mut saved) = self.lexer.save_until(Token::RightParen);
                let tok = self.lexer.next_useful();
                saved.push(tok.clone());

                let mut combined = CombinedLexers::new(&mut saved, self.lexer);

                // If we've a declaration then the next token...
                if tok == Token::SemiColon
                    || tok == Token::Equal
                    || tok == Token::LeftBrack
                    || tok == Token::LeftParen
                {
                    let tdp = TypeDeclaratorParser::new(&mut combined);
                    let (tok, typ) = tdp.parse(
                        Some(Token::LeftParen),
                        Some(DeclHint::Type(typ)),
                        true,
                        context,
                    )?;

                    Ok((tok, Some(DeclOrExpr::Decl(typ.unwrap()))))
                } else {
                    // finally we've an explicit type conversion
                    let mut ep = ExpressionParser::new(&mut combined, Token::Eof);
                    ep.push_operand(ExprNode::Type(Box::new(Type {
                        base: typ,
                        cv: CVQualifier::empty(),
                        pointers: None,
                    })));

                    let (tok, expr) = ep.parse(Some(Token::LeftParen), context)?;
                    Ok((tok, Some(DeclOrExpr::Expr(expr.unwrap()))))
                }
            } else {
                let tdp = TypeDeclaratorParser::new(self.lexer);
                let (tok, typ) = tdp.parse(Some(tok), Some(DeclHint::Type(typ)), true, context)?;

                Ok((tok, Some(DeclOrExpr::Decl(typ.unwrap()))))
            }
        } else if let Some(var) = var {
            let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
            ep.push_operand(var);
            let (tok, expr) = ep.parse(tok, context)?;

            Ok((tok, Some(DeclOrExpr::Expr(expr.unwrap()))))
        } else {
            let tp = TypeDeclaratorParser::new(self.lexer);
            let (tok, typ) = tp.parse(tok, None, true, context)?;

            if let Some(typ) = typ {
                return Ok((tok, Some(DeclOrExpr::Decl(typ))));
            }

            let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
            let (tok, expr) = ep.parse(tok, context)?;

            if let Some(expr) = expr {
                return Ok((tok, Some(DeclOrExpr::Expr(expr))));
            }

            Ok((tok, None))
        }
    }
}

#[cfg(test)]
mod tests {

    use std::rc::Rc;

    use super::super::function::*;
    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::mk_var;
    use crate::parser::array::*;
    use crate::parser::attributes::Attribute;
    use crate::parser::declarations::class::{self, *};
    use crate::parser::declarations::member::*;
    use crate::parser::declarations::pointer::*;
    use crate::parser::declarations::r#enum::{self, *};
    use crate::parser::expressions::{self, *};
    use crate::parser::literals::{self, *};
    use crate::parser::names::{self, operator, ConvBaseType, ConvType, Name};
    use crate::parser::types::{Primitive, UserDefined};
    use pretty_assertions::assert_eq;

    fn add_t_type(context: &mut Context) -> Rc<TypeDeclarator> {
        let t = Rc::new(TypeDeclarator {
            typ: Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            },
            specifier: Specifier::TYPEDEF,
            identifier: Identifier {
                identifier: Some(mk_id!("T")),
                attributes: None,
            },
            init: None,
            bitfield_size: None,
        });

        context.add_type_decl(Rc::clone(&t));
        t
    }

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
            let mut context = Context::default();
            let (_, (_, ty, _, _)) = p.parse(None, None, &mut context).unwrap();

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
            let mut context = Context::default();
            let (_, (_, ty, _, _)) = p.parse(None, None, &mut context).unwrap();
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
            let mut context = Context::default();
            let (_, (_, ty, _, _)) = p.parse(None, None, &mut context).unwrap();
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
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_pointer_paren() {
        let mut l = Lexer::<DefaultContext>::new(b"int (*x) = nullptr");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_pointer_ud() {
        let mut l = Lexer::<DefaultContext>::new(b"volatile A::B::C * x = nullptr");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(Box::new(UserDefined {
                        name: mk_id!("A", "B", "C"),
                        typ: UDType::Indirect(TypeToFix::default())
                    })),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_list_init() {
        let mut l = Lexer::<DefaultContext>::new(b"const int x{314}");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                init: Some(Initializer::Brace(vec![ExprNode::Integer(Box::new(
                    literals::Integer {
                        value: IntLiteral::Int(314)
                    }
                )),])),
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_const_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"signed short volatile int * const x = NULL");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                init: Some(Initializer::Equal(ExprNode::Variable(Box::new(mk_var!(
                    "NULL"
                ))))),
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_double_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** x");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_triple_pointer() {
        let mut l = Lexer::<DefaultContext>::new(b"char ** const * x");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_triple_pointer_ud_type() {
        let mut l = Lexer::<DefaultContext>::new(b"A::B ** const * x");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(Box::new(UserDefined {
                        name: mk_id!("A", "B"),
                        typ: UDType::Indirect(TypeToFix::default())
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int & x");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_rvalue_reference() {
        let mut l = Lexer::<DefaultContext>::new(b"int && x");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_simple_rvalue_reference_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"int &&");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_double_pointer_abstract() {
        let mut l = Lexer::<DefaultContext>::new(b"char **");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_array_ptr() {
        let mut l = Lexer::<DefaultContext>::new(b"int (*foo[2]) [3]");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_no_name() {
        let mut l = Lexer::<DefaultContext>::new(b"int *()");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_1() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x)");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: Rc::new(TypeDeclarator {
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
                                init: None,
                                bitfield_size: None,
                            }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_ptr_fun_1() {
        let mut l = Lexer::<DefaultContext>::new(b"int (**) (int x)");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: Rc::new(TypeDeclarator {
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
                                init: None,
                                bitfield_size: None,
                            }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_1_ptr() {
        let mut l = Lexer::<DefaultContext>::new(b"double ** foo(int x)");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                            decl: Rc::new(TypeDeclarator {
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
                                init: None,
                                bitfield_size: None,
                            }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_2() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo::bar(int x, const double * const y)");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                                decl: Rc::new(TypeDeclarator {
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
                                    init: None,
                                    bitfield_size: None,
                                }),
                            },
                            Parameter {
                                attributes: None,
                                decl: Rc::new(TypeDeclarator {
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
                                    init: None,
                                    bitfield_size: None,
                                }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_1_init() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo(int x = 123)");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: Rc::new(TypeDeclarator {
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
                                )))),
                                bitfield_size: None,
                            }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_fun_1_init_extra() {
        let mut l = Lexer::<DefaultContext>::new(
            b"int foo([[attribute]] int x = 123) const && throw(A, B) [[noreturn]] -> C",
        );
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                            decl: Rc::new(TypeDeclarator {
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
                                )))),
                                bitfield_size: None,
                            }),
                        }],
                        cv: CVQualifier::CONST,
                        refq: RefQualifier::RValue,
                        except: Some(Exception::Throw(Some(vec![
                            ExprNode::Variable(Box::new(mk_var!("A"))),
                            ExprNode::Variable(Box::new(mk_var!("B"))),
                        ],))),
                        attributes: Some(vec![Attribute {
                            namespace: None,
                            name: "noreturn".to_string(),
                            arg: None,
                            has_using: false,
                        }]),
                        trailing: Some(Type {
                            base: BaseType::UD(Box::new(UserDefined {
                                name: mk_id!("C"),
                                typ: UDType::Indirect(TypeToFix::default())
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_array() {
        let mut l = Lexer::<DefaultContext>::new(b"int foo[123]");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_array_no_size() {
        let mut l = Lexer::<DefaultContext>::new(b"unsigned short foo[]");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Array(Box::new(Array {
                        base: Some(Type {
                            base: BaseType::Primitive(Primitive::UnsignedShort),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        dimensions: vec![Dimension {
                            size: None,
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_array_no_size_init() {
        let mut l = Lexer::<DefaultContext>::new(b"static unsigned short foo[] = { 1, 2 }");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Array(Box::new(Array {
                        base: Some(Type {
                            base: BaseType::Primitive(Primitive::UnsignedShort),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        dimensions: vec![Dimension {
                            size: None,
                            attributes: None,
                        }],
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::STATIC,
                identifier: Identifier {
                    identifier: Some(mk_id!("foo")),
                    attributes: None
                },
                init: Some(Initializer::Equal(ExprNode::ListInit(Box::new(vec![
                    ExprNode::Integer(Box::new(literals::Integer {
                        value: IntLiteral::Int(1)
                    })),
                    ExprNode::Integer(Box::new(literals::Integer {
                        value: IntLiteral::Int(2)
                    })),
                ])))),
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_enum() {
        let mut l = Lexer::<DefaultContext>::new(b"typedef enum A { a } B");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Enum(Box::new(Enum {
                        kind: r#enum::Kind::None,
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
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_struct() {
        let mut l = Lexer::<DefaultContext>::new(b"typedef struct { int a; } A");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Class(Box::new(Class {
                        kind: class::Kind::Struct,
                        attributes: None,
                        name: None,
                        r#final: false,
                        bases: None,
                        body: Some(ClassBody {
                            public: vec![Member::Type(Rc::new(TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: Some(mk_id!("a")),
                                    attributes: None,
                                },
                                init: None,
                                bitfield_size: None,
                            })),],
                            protected: vec![],
                            private: vec![],
                        }),
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::TYPEDEF,
                identifier: Identifier {
                    identifier: Some(mk_id!("A")),
                    attributes: None,
                },
                init: None,
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_operator_unary() {
        let mut l = Lexer::<DefaultContext>::new(b"A B::operator+()");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::UD(Box::new(UserDefined {
                                name: mk_id!("A"),
                                typ: UDType::Indirect(TypeToFix::default())
                            })),
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
                                expressions::Operator::Plus
                            ))),
                        ]
                    }),
                    attributes: None
                },
                init: None,
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_operator_conv() {
        let mut l = Lexer::<DefaultContext>::new(b"operator A()");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                        names: vec![Name::Operator(Box::new(operator::Operator::Conv(
                            ConvType {
                                base: ConvBaseType::UD(Box::new(UserDefined {
                                    name: mk_id!("A"),
                                    typ: UDType::Indirect(TypeToFix::default())
                                })),
                                cv: CVQualifier::empty(),
                                pointers: None,
                            },
                        ))),]
                    }),
                    attributes: None
                },
                init: None,
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_operator_conv_scoped() {
        let mut l = Lexer::<DefaultContext>::new(b"A::operator B()");
        let p = TypeDeclaratorParser::new(&mut l);
        let mut context = Context::default();
        let (_, decl) = p.parse(None, None, true, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            Rc::new(TypeDeclarator {
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
                            Name::Operator(Box::new(operator::Operator::Conv(ConvType {
                                base: ConvBaseType::UD(Box::new(UserDefined {
                                    name: mk_id!("B"),
                                    typ: UDType::Indirect(TypeToFix::default())
                                })),
                                cv: CVQualifier::empty(),
                                pointers: None,
                            },))),
                        ]
                    }),
                    attributes: None
                },
                init: None,
                bitfield_size: None,
            })
        );
    }

    #[test]
    fn test_ambiguity_1() {
        let mut l = Lexer::<DefaultContext>::new(b"T(a)->m = 7;");
        let p = DeclOrExprParser::new(&mut l);
        let mut context = Context::default();
        let t = add_t_type(&mut context);

        let (_, decl) = p.parse(None, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            DeclOrExpr::Expr(node!(BinaryOp {
                op: Operator::Assign,
                arg1: node!(BinaryOp {
                    op: Operator::Arrow,
                    arg1: node!(CallExpr {
                        callee: node!(Type {
                            base: BaseType::UD(Box::new(UserDefined {
                                name: mk_id!("T"),
                                typ: UDType::Direct(t),
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![node!(Variable {
                            name: mk_id!("a"),
                            decl: VarDecl::Indirect(TypeToFix::default()),
                        })],
                    }),
                    arg2: node!(Variable {
                        name: mk_id!("m"),
                        decl: VarDecl::Indirect(TypeToFix::default()),
                    }),
                }),
                arg2: node!(Integer {
                    value: IntLiteral::Int(7)
                }),
            }))
        );
    }

    #[test]
    fn test_ambiguity_2() {
        let mut l = Lexer::<DefaultContext>::new(b"T(a)++;");
        let p = DeclOrExprParser::new(&mut l);
        let mut context = Context::default();
        let t = add_t_type(&mut context);

        let (_, decl) = p.parse(None, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            DeclOrExpr::Expr(node!(UnaryOp {
                op: Operator::PostInc,
                arg: node!(CallExpr {
                    callee: node!(Type {
                        base: BaseType::UD(Box::new(UserDefined {
                            name: mk_id!("T"),
                            typ: UDType::Direct(t),
                        })),
                        cv: CVQualifier::empty(),
                        pointers: None,
                    }),
                    params: vec![node!(Variable {
                        name: mk_id!("a"),
                        decl: VarDecl::Indirect(TypeToFix::default()),
                    })],
                }),
            }))
        );
    }

    #[test]
    fn test_ambiguity_3() {
        let mut l = Lexer::<DefaultContext>::new(b"T(*d)(int)");
        let p = DeclOrExprParser::new(&mut l);
        let mut context = Context::default();
        let t = add_t_type(&mut context);

        let (_, decl) = p.parse(None, &mut context).unwrap();
        let decl = decl.unwrap();

        assert_eq!(
            decl,
            DeclOrExpr::Decl(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::UD(Box::new(UserDefined {
                                name: mk_id!("T"),
                                typ: UDType::Direct(t),
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: Rc::new(TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Int),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: Identifier {
                                    identifier: None,
                                    attributes: None
                                },
                                init: None,
                                bitfield_size: None,
                            }),
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
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Pointer,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("d")),
                    attributes: None
                },
                init: None,
                bitfield_size: None,
            }))
        );
    }
}
