// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::expr::{CallExpr, ExprNode, ExpressionParser, LastKind};
use super::operator::Operator;
use super::params::ParametersParser;
use crate::lexer::lexer::Token;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::declarations::{
    DeclHint, MSModifier, NoPtrDeclaratorParser, Pointer, PointerDeclaratorParser, PtrKind,
    Specifier, TypeDeclarator, TypeDeclaratorParser,
};
use crate::parser::name::{Qualified, QualifiedParser};
use crate::parser::types::{BaseType, CVQualifier, Modifier, Primitive, Type};
use crate::parser::Context;

enum CastType {
    Qual(Qualified),
    Prim(Primitive),
}

impl CastType {
    fn node(self) -> ExprNode {
        match self {
            CastType::Qual(q) => ExprNode::Qualified(Box::new(q)),
            CastType::Prim(p) => ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(p),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
        }
    }

    fn typ(self) -> BaseType {
        match self {
            CastType::Qual(q) => BaseType::UD(q),
            CastType::Prim(p) => BaseType::Primitive(p),
        }
    }
}

impl<'a, 'b, PC: PreprocContext> ExpressionParser<'a, 'b, PC> {
    fn handle_paren_after_type(&mut self, ctyp: CastType, context: &mut Context) -> Option<Token> {
        // (T (...: we may have a function/array pointer
        let pdp = PointerDeclaratorParser::new(self.lexer);
        let (tok, pointers) = pdp.parse(None, None, context);

        let pointers = if let Some(pointers) = pointers {
            pointers
        } else {
            let pp = ParametersParser::new(self.lexer, Token::RightParen);
            let (tok, params) = pp.parse(tok, None, context);

            self.operators.push(Operator::Parenthesis);
            self.level += 1;
            self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                callee: ctyp.node(),
                params: params.unwrap(),
            })));
            self.last = LastKind::Operand;
            return tok;
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
            let (tok, first) = ep.parse(Some(tok), context);

            let pp = ParametersParser::new(self.lexer, Token::RightParen);
            let (tok, params) = pp.parse(tok, first, context);

            self.operators.push(Operator::Parenthesis);
            self.level += 1;
            self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                callee: ctyp.node(),
                params: params.unwrap(),
            })));
            self.last = LastKind::Operand;
            return tok;
        }

        // (T (***) ...: so we've a function/array pointer
        let npdp = NoPtrDeclaratorParser::new(self.lexer);
        let typ = Type {
            base: ctyp.typ(),
            cv: CVQualifier::empty(),
            pointers: None,
        };
        let (tok, decl) = npdp.parse(None, typ, Specifier::empty(), false, false, context);
        let mut typ = decl.unwrap().typ;
        typ.pointers = Some(pointers);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::RightParen {
            self.operands.push(ExprNode::Type(Box::new(typ)));
            self.push_operator(Operator::Cast);
        }

        None
    }

    pub(super) fn parse_left_paren(&mut self, context: &mut Context) -> Option<Token> {
        let tok = self.lexer.next_useful();
        if CVQualifier::is_cv(&tok) || TypeDeclarator::is_type_part(&tok) {
            // (const ...
            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) = tdp.parse(Some(tok), None, false, context);

            let typ = decl.unwrap().typ;
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

            if tok == Token::RightParen {
                self.operands.push(ExprNode::Type(Box::new(typ)));
                self.push_operator(Operator::Cast);
                self.last = LastKind::Operator;
            }
            return None;
        }

        if Modifier::is_primitive_part(&tok) {
            // (int...
            let mut modif = Modifier::empty();
            modif.from_tok(&tok);

            let tok = self.lexer.next_useful();
            if tok == Token::LeftParen {
                // (int(...: not a cast
                self.handle_paren_after_type(CastType::Prim(modif.to_primitive()), context);
                return None;
            }

            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) = tdp.parse(Some(tok), Some(DeclHint::Modifier(modif)), false, context);

            let typ = decl.unwrap().typ;
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

            if tok == Token::RightParen {
                self.operands.push(ExprNode::Type(Box::new(typ)));
                self.push_operator(Operator::Cast);
                self.last = LastKind::Operator;
            }
            return None;
        }

        // TODO: handle case where id is final, override, ...
        if let Token::Identifier(id) = tok {
            let qp = QualifiedParser::new(self.lexer);
            let (tok, qual) = qp.parse(None, Some(id), context);
            let qual = qual.unwrap();

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if let Some(kind) = PtrKind::from_tok(&tok) {
                // (T *...)
                let tok = self.lexer.next_useful();
                if CVQualifier::is_cv(&tok) || PtrKind::is_ptr(&tok) {
                    // (T * const... or (T **... => we've a type !
                    let pdp = PointerDeclaratorParser::new(self.lexer);
                    let (tok, pointers) = pdp.parse(Some(tok), Some(kind), context);

                    let typ = Type {
                        base: BaseType::UD(qual),
                        cv: CVQualifier::empty(),
                        pointers,
                    };

                    let tdp = TypeDeclaratorParser::new(self.lexer);
                    let (tok, decl) = tdp.parse(tok, Some(DeclHint::Type(typ)), false, context);

                    let typ = decl.unwrap().typ;
                    let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                    if tok == Token::RightParen {
                        self.operands.push(ExprNode::Type(Box::new(typ)));
                        self.push_operator(Operator::Cast);
                    }
                    return None;
                } else if tok == Token::RightParen {
                    // (T *)
                    let typ = Type {
                        base: BaseType::UD(qual),
                        cv: CVQualifier::empty(),
                        pointers: Some(vec![Pointer {
                            kind,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        }]),
                    };

                    self.operands.push(ExprNode::Type(Box::new(typ)));
                    self.push_operator(Operator::Cast);
                    return None;
                } else if CVQualifier::is_cv(&tok) {
                    // (T const...
                    let tdp = TypeDeclaratorParser::new(self.lexer);
                    let (tok, decl) =
                        tdp.parse(Some(tok), Some(DeclHint::Name(Some(qual))), false, context);

                    let typ = decl.unwrap().typ;
                    let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                    if tok == Token::RightParen {
                        self.operands.push(ExprNode::Type(Box::new(typ)));
                        self.push_operator(Operator::Cast);
                    }
                    return None;
                } else {
                    // Not a pointer => bin operation: mul, bitand, and
                    self.operators.push(Operator::Parenthesis);
                    self.level += 1;
                    self.operands.push(ExprNode::Qualified(Box::new(qual)));

                    let op = match kind {
                        PtrKind::Pointer => Operator::Mul,
                        PtrKind::Reference => Operator::BitAnd,
                        PtrKind::RValue => Operator::And,
                    };
                    self.operators.push(op);
                    self.last = LastKind::Operator;
                    return Some(tok);
                }
            } else if tok == Token::LeftParen {
                // (T (...: we may have a function/array pointer
                return self.handle_paren_after_type(CastType::Qual(qual), context);
            } else if tok == Token::RightParen {
                // (T)
                let tok = self.lexer.next_useful();

                // Problematic operators are: ++, --, +, -, &, &&, *, function call
                // we've something like (T) - a * 3....
                // so here return FakeCast(T, -a * 3 ...)
                // once T is known then transform the node according to operator precedence
                // here if T is a type node will become Cast(T, -a * 3)
                // else Sub(T, a * 3)
                // I don't know if it's correct... check that
                let tok = match tok {
                    Token::Plus
                    | Token::Minus
                    | Token::And
                    | Token::AndAnd
                    | Token::Star
                    | Token::LeftParen
                    | Token::PlusPlus
                    | Token::MinusMinus => {
                        // record token and parse again when we've enough info
                        // to guess if the name is a type or not
                        None
                    }
                    Token::Identifier(_)
                    | Token::Not
                    | Token::LiteralChar(_)
                    | Token::LiteralLChar(_)
                    | Token::LiteralUUChar(_)
                    | Token::LiteralUChar(_)
                    | Token::LiteralU8Char(_)
                    | Token::LiteralCharUD(_)
                    | Token::LiteralLCharUD(_)
                    | Token::LiteralUUCharUD(_)
                    | Token::LiteralUCharUD(_)
                    | Token::LiteralU8CharUD(_)
                    | Token::LiteralDouble(_)
                    | Token::LiteralLongDouble(_)
                    | Token::LiteralFloat(_)
                    | Token::LiteralFloatUD(_)
                    | Token::LiteralInt(_)
                    | Token::LiteralUInt(_)
                    | Token::LiteralLong(_)
                    | Token::LiteralLongLong(_)
                    | Token::LiteralULong(_)
                    | Token::LiteralULongLong(_)
                    | Token::LiteralIntUD(_)
                    | Token::LiteralString(_)
                    | Token::LiteralLString(_)
                    | Token::LiteralUString(_)
                    | Token::LiteralUUString(_)
                    | Token::LiteralU8String(_)
                    | Token::LiteralRString(_)
                    | Token::LiteralLRString(_)
                    | Token::LiteralURString(_)
                    | Token::LiteralUURString(_)
                    | Token::LiteralU8RString(_)
                    | Token::LiteralStringUD(_)
                    | Token::LiteralLStringUD(_)
                    | Token::LiteralUStringUD(_)
                    | Token::LiteralUUStringUD(_)
                    | Token::LiteralU8StringUD(_)
                    | Token::LiteralRStringUD(_)
                    | Token::LiteralLRStringUD(_)
                    | Token::LiteralURStringUD(_)
                    | Token::LiteralUURStringUD(_)
                    | Token::LiteralU8RStringUD(_)
                    | Token::Tilde
                    | Token::NotKw
                    | Token::This
                    | Token::True
                    | Token::False => {
                        let typ = Type {
                            base: BaseType::UD(qual),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        };

                        self.operands.push(ExprNode::Type(Box::new(typ)));
                        self.push_operator(Operator::Cast);
                        Some(tok)
                    }
                    _ => {
                        self.operands.push(ExprNode::Qualified(Box::new(qual)));
                        self.last = LastKind::Operand;
                        Some(tok)
                    }
                };
                return tok;
            } else {
                self.operators.push(Operator::Parenthesis);
                self.level += 1;
                self.operands.push(ExprNode::Qualified(Box::new(qual)));
                self.last = LastKind::Operand;

                return Some(tok);
            }
        }

        self.operators.push(Operator::Parenthesis);
        self.last = LastKind::Operator;

        Some(tok)
    }
}

#[cfg(test)]
mod tests {

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
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_primitive_paren() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int)(a)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_primitive_pointer() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int *)a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

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
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_type_pointer() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T *)a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::UD(mk_id!("T")),
                cv: CVQualifier::empty(),
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_fun_pointer_int() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int (*) (int))a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

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
                        decl: TypeDeclarator {
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
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_fun_pointer_type() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T (*) (int))a");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Cast,
            arg1: ExprNode::Type(Box::new(Type {
                base: BaseType::Function(Box::new(Function {
                    return_type: Some(Type {
                        base: BaseType::UD(mk_id!("T")),
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
                                identifier: None,
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
                pointers: Some(vec![Pointer {
                    kind: PtrKind::Pointer,
                    attributes: None,
                    cv: CVQualifier::empty(),
                    ms: MSModifier::empty(),
                }]),
            })),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_1() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int(a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            params: vec![ExprNode::Qualified(Box::new(mk_id!("a"))),],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T(a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Qualified(Box::new(mk_id!("T"))),
            params: vec![ExprNode::Qualified(Box::new(mk_id!("a"))),],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_3() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T(*a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Qualified(Box::new(mk_id!("T"))),
            params: vec![node!(UnaryOp {
                op: Operator::Indirection,
                arg: ExprNode::Qualified(Box::new(mk_id!("a"))),
            })],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_4() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(int(&a))");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Type(Box::new(Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            })),
            params: vec![node!(UnaryOp {
                op: Operator::AddressOf,
                arg: ExprNode::Qualified(Box::new(mk_id!("a"))),
            })],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_cast_invalid_5() {
        let mut lexer = Lexer::<DefaultContext>::new(b"(T * a)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Mul,
            arg1: ExprNode::Qualified(Box::new(mk_id!("T"))),
            arg2: ExprNode::Qualified(Box::new(mk_id!("a"))),
        });

        assert_eq!(node, expected);
    }
}
