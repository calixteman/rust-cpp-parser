// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;

use super::expr::{CallExpr, ExprNode, ExpressionParser, LastKind, VarDecl, Variable};
use super::operator::Operator;
use super::params::ParametersParser;
use crate::lexer::{TLexer, Token};
use crate::parser::context::{Context, SearchResult, TypeToFix};
use crate::parser::declarations::{
    DeclHint, NoPtrDeclaratorParser, PointerDeclaratorParser, PtrKind, Specifier, TypeDeclarator,
    TypeDeclaratorParser,
};
use crate::parser::errors::ParserError;
use crate::parser::name::QualifiedParser;
use crate::parser::types::{BaseType, CVQualifier, Modifier, Primitive, Type, UDType, UserDefined};

enum CastType {
    UD(BaseType),
    Prim(Primitive),
}

impl CastType {
    fn node(self) -> ExprNode {
        match self {
            CastType::UD(ud) => ExprNode::Type(Box::new(Type {
                base: ud,
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            CastType::Prim(p) => ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(p),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
        }
    }

    fn typ(self) -> BaseType {
        match self {
            CastType::UD(ud) => ud,
            CastType::Prim(p) => BaseType::Primitive(p),
        }
    }
}

impl<'a, L: TLexer> ExpressionParser<'a, L> {
    fn handle_paren_after_type(
        &mut self,
        ctyp: CastType,
        context: &mut Context,
    ) -> Result<Option<Token>, ParserError> {
        // (T (...: we may have a function/array pointer
        let pdp = PointerDeclaratorParser::new(self.lexer);
        let (tok, pointers) = pdp.parse(None, None, context)?;

        let pointers = if let Some(pointers) = pointers {
            pointers
        } else {
            let pp = ParametersParser::new(self.lexer, Token::RightParen);
            let (tok, params) = pp.parse(tok, None, context)?;

            self.operators.push(Operator::Parenthesis);
            self.level += 1;
            self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                callee: ctyp.node(),
                params: params.unwrap(),
            })));
            self.last = LastKind::Operand;
            return Ok(tok);
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            // (T (***a...: function call
            let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
            for p in pointers {
                match p.kind {
                    PtrKind::Pointer => {
                        ep.operators.push(Operator::Indirection);
                    }
                    PtrKind::Reference => {
                        ep.operators.push(Operator::AddressOf);
                    }
                    PtrKind::RValue => {
                        ep.operators.push(Operator::AddressOfLabel);
                    }
                }
            }
            ep.last = LastKind::Operator;
            // Get the first argument
            let (tok, first) = ep.parse(Some(tok), context)?;

            let pp = ParametersParser::new(self.lexer, Token::RightParen);
            let (tok, params) = pp.parse(tok, first, context)?;

            self.operators.push(Operator::Parenthesis);
            self.level += 1;
            self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                callee: ctyp.node(),
                params: params.unwrap(),
            })));
            self.last = LastKind::Operand;
            return Ok(tok);
        }

        // (T (***) ...: so we've a function/array pointer
        let npdp = NoPtrDeclaratorParser::new(self.lexer);
        let typ = Type {
            base: ctyp.typ(),
            cv: CVQualifier::empty(),
            pointers: None,
        };
        let (tok, decl, _, _) = npdp.parse(None, typ, Specifier::empty(), false, false, context)?;
        let mut typ = decl.unwrap().typ;
        typ.pointers = Some(pointers);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::RightParen {
            self.operands.push(ExprNode::Type(Box::new(typ)));
            self.push_operator(Operator::Cast);
        }

        Ok(None)
    }

    pub(super) fn parse_left_paren(
        &mut self,
        context: &mut Context,
    ) -> Result<Option<Token>, ParserError> {
        let tok = self.lexer.next_useful();
        if CVQualifier::is_cv(&tok) || TypeDeclarator::is_type_part(&tok) {
            // (const ... => cast-operation
            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) = tdp.parse(Some(tok), None, false, context)?;

            let typ = Rc::try_unwrap(decl.unwrap()).unwrap().typ;
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

            if tok == Token::RightParen {
                self.operands.push(ExprNode::Type(Box::new(typ)));
                self.push_operator(Operator::Cast);
                self.last = LastKind::Operator;
            }
            return Ok(None);
        }

        if Modifier::is_primitive_part(&tok) {
            // (int ...
            let mut modif = Modifier::empty();
            modif.from_tok(&tok);

            let tok = self.lexer.next_useful();
            if tok == Token::LeftParen {
                // (int(**)) or (int(123)...
                self.handle_paren_after_type(CastType::Prim(modif.to_primitive()), context)?;
                return Ok(None);
            }

            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) =
                tdp.parse(Some(tok), Some(DeclHint::Modifier(modif)), false, context)?;

            let typ = Rc::try_unwrap(decl.unwrap()).unwrap().typ;
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

            if tok == Token::RightParen {
                self.operands.push(ExprNode::Type(Box::new(typ)));
                self.push_operator(Operator::Cast);
                self.last = LastKind::Operator;
            }
            return Ok(None);
        }

        // TODO: handle case where id is final, override, ...
        match tok {
            Token::Identifier(id) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, qual) = qp.parse(None, Some(id), context)?;
                let qual = qual.unwrap();

                if let Some(res) = context.search(Some(&qual)) {
                    let (typ, var) = match res {
                        SearchResult::Var(var) => (
                            None,
                            Some(ExprNode::Variable(Box::new(Variable {
                                name: qual,
                                decl: VarDecl::Direct(var),
                            }))),
                        ),
                        SearchResult::IncompleteVar(var) => (
                            None,
                            Some(ExprNode::Variable(Box::new(Variable {
                                name: qual,
                                decl: VarDecl::Indirect(var),
                            }))),
                        ),
                        SearchResult::Type(typ) => (
                            Some(BaseType::UD(Box::new(UserDefined {
                                name: qual,
                                typ: UDType::Direct(typ),
                            }))),
                            None,
                        ),
                        SearchResult::IncompleteType(typ) => (
                            Some(BaseType::UD(Box::new(UserDefined {
                                name: qual,
                                typ: UDType::Indirect(typ),
                            }))),
                            None,
                        ),
                    };

                    if let Some(typ) = typ {
                        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                        if tok == Token::LeftParen {
                            self.handle_paren_after_type(CastType::UD(typ), context)?;
                            return Ok(None);
                        }

                        let tdp = TypeDeclaratorParser::new(self.lexer);
                        let (tok, decl) =
                            tdp.parse(Some(tok), Some(DeclHint::Type(typ)), false, context)?;

                        let typ = Rc::try_unwrap(decl.unwrap()).unwrap().typ;
                        self.operands.push(ExprNode::Type(Box::new(typ)));

                        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                        if tok != Token::RightParen {
                            return Err(ParserError::InvalidCast {
                                sp: self.lexer.span(),
                            });
                        }

                        // We've a cast for sure
                        self.push_operator(Operator::Cast);
                        self.last = LastKind::Operator;
                        return Ok(None);
                    } else {
                        let var = var.unwrap();
                        self.operators.push(Operator::Parenthesis);
                        self.level += 1;
                        self.operands.push(var);
                        self.last = LastKind::Operand;
                        return Ok(tok);
                    }
                } else {
                    // TODO: so the id doesn't exist => error
                    self.operators.push(Operator::Parenthesis);
                    self.level += 1;
                    self.operands.push(ExprNode::Variable(Box::new(Variable {
                        name: qual,
                        decl: VarDecl::Indirect(TypeToFix::default()),
                    })));
                    self.last = LastKind::Operand;

                    return Ok(tok);
                }
            }
            tok => {
                self.operators.push(Operator::Parenthesis);
                self.last = LastKind::Operator;

                Ok(Some(tok))
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::lexer::Lexer;
    use crate::parser::declarations::*;
    use crate::parser::expressions::*;
    use crate::parser::names::Qualified;
    use crate::parser::types::Primitive;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_cast_primitive() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int)a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_primitive_paren() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int)(a)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_primitive_pointer() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int *)a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_type_pointer() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T *)a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
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

        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::UD(Box::new(UserDefined {
                    name: mk_id!("T"),
                    typ: UDType::Direct(Rc::clone(&t))
                })),
                cv: CVQualifier::empty(),
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_fun_pointer_int() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int (*) (int))a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
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
                    body: RefCell::new(None)
                })),
                cv: CVQualifier::empty(),
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_fun_pointer_type() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T (*) (int))a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
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

        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Function(Box::new(Function {
                    return_type: Some(Type {
                        base: BaseType::UD(Box::new(UserDefined {
                            name: mk_id!("T"),
                            typ: UDType::Direct(Rc::clone(&t))
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
                    body: RefCell::new(None)
                })),
                cv: CVQualifier::empty(),
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_1() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int(a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            params: vec![ExprNode::Variable(Box::new(mk_var!("a"))),],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T(a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Variable(Box::new(mk_var!("T"))),
            params: vec![ExprNode::Variable(Box::new(mk_var!("a"))),],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_3() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T(*a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Variable(Box::new(mk_var!("T"))),
            params: vec![node!(UnaryOp {
                op: Operator::Indirection,
                arg: ExprNode::Variable(Box::new(mk_var!("a"))),
            })],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_4() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int(&a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            params: vec![node!(UnaryOp {
                op: Operator::AddressOf,
                arg: ExprNode::Variable(Box::new(mk_var!("a"))),
            })],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_5() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T * a)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Mul,
            arg1: ExprNode::Variable(Box::new(mk_var!("T"))),
            arg2: ExprNode::Variable(Box::new(mk_var!("a"))),
        });

        assert_eq!(node, expected);
    }
}
