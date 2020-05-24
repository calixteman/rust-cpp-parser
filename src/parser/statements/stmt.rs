// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::{
    Case, CaseStmtParser, Compound, CompoundStmtParser, Default, DefaultStmtParser, Do,
    DoStmtParser, For, ForRange, ForRes, ForStmtParser, Goto, GotoStmtParser, If, IfStmtParser,
    Return, ReturnStmtParser, Switch, SwitchStmtParser, Try, TryStmtParser, While, WhileStmtParser,
};
use crate::lexer::{TLexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::context::Context;
use crate::parser::declarations::decl::{Declaration, DeclarationParser};
use crate::parser::declarations::types::{DeclHint, TypeDeclaratorParser};
use crate::parser::dump::Dump;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::names::QualifiedParser;

#[derive(Clone, Debug, PartialEq)]
pub struct Break {
    pub(crate) attributes: Option<Attributes>,
}

impl Dump for Break {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "break", prefix, last, stdout, attributes);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Continue {
    pub(crate) attributes: Option<Attributes>,
}

impl Dump for Continue {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "continue", prefix, last, stdout, attributes);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Compound(Box<Compound>),
    Return(Box<Return>),
    If(Box<If>),
    Switch(Box<Switch>),
    Case(Box<Case>),
    Default(Box<Default>),
    Do(Box<Do>),
    While(Box<While>),
    Continue(Box<Continue>),
    Break(Box<Break>),
    Goto(Box<Goto>),
    Try(Box<Try>),
    For(Box<For>),
    ForRange(Box<ForRange>),
    Declaration(Box<Declaration>),
    Expression(Box<ExprNode>),
    Empty,
}

impl Dump for Statement {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::Compound(x) => dump!(x),
            Self::Return(x) => dump!(x),
            Self::If(x) => dump!(x),
            Self::Switch(x) => dump!(x),
            Self::Case(x) => dump!(x),
            Self::Default(x) => dump!(x),
            Self::Do(x) => dump!(x),
            Self::While(x) => dump!(x),
            Self::Continue(x) => dump!(x),
            Self::Break(x) => dump!(x),
            Self::Goto(x) => dump!(x),
            Self::Try(x) => dump!(x),
            Self::For(x) => dump!(x),
            Self::ForRange(x) => dump!(x),
            Self::Declaration(x) => dump!(x),
            Self::Expression(x) => dump!(x),
            Self::Empty => dump_str!(name, "empty", Cyan, prefix, last, stdout),
        }
    }
}

#[macro_export]
macro_rules! check_semicolon {
    ( $self:expr, $tok:expr ) => {
        let tok = $tok.unwrap_or_else(|| $self.lexer.next_useful());
        if tok != Token::SemiColon {
            unreachable!("Invalid token in statements: {:?}", tok);
        }
    };
}

#[macro_export]
macro_rules! check_semicolon_or_not {
    ( $self:expr, $tok:expr, $decl: expr ) => {
        if let Some(decl) = $decl {
            let tok = if decl.has_semicolon() {
                check_semicolon!($self, $tok);
                None
            } else {
                $tok
            };
            (
                tok,
                Some(crate::parser::statements::Statement::Declaration(Box::new(
                    decl,
                ))),
            )
        } else {
            ($tok, None)
        }
    };
}

pub struct StatementParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> StatementParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Statement>) {
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok, context);
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok {
            Token::Return => {
                let rp = ReturnStmtParser::new(self.lexer);
                let (tok, ret) = rp.parse(attributes, context);
                check_semicolon!(self, tok);
                (None, Some(Statement::Return(Box::new(ret.unwrap()))))
            }
            Token::LeftBrace => {
                let cp = CompoundStmtParser::new(self.lexer);
                let (_, compound) = cp.parse(attributes, context);
                (None, Some(Statement::Compound(Box::new(compound.unwrap()))))
            }
            Token::If => {
                let ip = IfStmtParser::new(self.lexer);
                let (tok, ifs) = ip.parse(attributes, context);
                (tok, Some(Statement::If(Box::new(ifs.unwrap()))))
            }
            Token::Switch => {
                let sp = SwitchStmtParser::new(self.lexer);
                let (tok, switch) = sp.parse(attributes, context);
                (tok, Some(Statement::Switch(Box::new(switch.unwrap()))))
            }
            Token::While => {
                let wp = WhileStmtParser::new(self.lexer);
                let (tok, wh) = wp.parse(attributes, context);
                (tok, Some(Statement::While(Box::new(wh.unwrap()))))
            }
            Token::Do => {
                let dp = DoStmtParser::new(self.lexer);
                let (tok, d) = dp.parse(attributes, context);
                (tok, Some(Statement::Do(Box::new(d.unwrap()))))
            }
            Token::For => {
                let fp = ForStmtParser::new(self.lexer);
                let (tok, f) = fp.parse(attributes, context);

                match f.unwrap() {
                    ForRes::Normal(f) => (tok, Some(Statement::For(Box::new(f)))),
                    ForRes::Range(f) => (tok, Some(Statement::ForRange(Box::new(f)))),
                }
            }
            Token::Break => {
                check_semicolon!(self, None);
                (None, Some(Statement::Break(Box::new(Break { attributes }))))
            }
            Token::Continue => {
                check_semicolon!(self, None);
                (
                    None,
                    Some(Statement::Continue(Box::new(Continue { attributes }))),
                )
            }
            Token::Goto => {
                let gp = GotoStmtParser::new(self.lexer);
                let (tok, goto) = gp.parse(attributes, context);
                check_semicolon!(self, tok);
                (None, Some(Statement::Goto(Box::new(goto.unwrap()))))
            }
            Token::Try => {
                let tp = TryStmtParser::new(self.lexer);
                let (tok, t) = tp.parse(attributes, context);

                (tok, Some(Statement::Try(Box::new(t.unwrap()))))
            }
            Token::Case => {
                let cp = CaseStmtParser::new(self.lexer);
                let (tok, case) = cp.parse(attributes, context);
                (tok, Some(Statement::Case(Box::new(case.unwrap()))))
            }
            Token::Default => {
                let dp = DefaultStmtParser::new(self.lexer);
                let (tok, default) = dp.parse(attributes, context);
                (tok, Some(Statement::Default(Box::new(default.unwrap()))))
            }
            Token::SemiColon => (None, Some(Statement::Empty)),
            Token::Identifier(id) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, name) = qp.parse(None, Some(id), context);

                let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                let (tok, stmt) = if TypeDeclaratorParser::<L>::is_decl_part(&tok) {
                    let dp = DeclarationParser::new(self.lexer);
                    let hint = DeclHint::Name(name);
                    let (tok, decl) = dp.parse(Some(tok), Some(hint), context);

                    (tok, Some(Statement::Declaration(Box::new(decl.unwrap()))))
                } else {
                    let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                    let (tok, expr) = ep.parse_with_id(Some(tok), name.unwrap(), context);

                    (tok, Some(Statement::Expression(Box::new(expr.unwrap()))))
                };
                check_semicolon!(self, tok);
                (None, stmt)
            }
            _ => {
                let dp = DeclarationParser::new(self.lexer);
                let (tok, decl) = dp.parse(Some(tok), None, context);
                let (tok, decl) = check_semicolon_or_not!(self, tok, decl);

                if decl.is_some() {
                    return (tok, decl);
                }

                let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                let (tok, expr) = ep.parse(tok, context);

                if let Some(expr) = expr {
                    check_semicolon!(self, tok);
                    return (None, Some(Statement::Expression(Box::new(expr))));
                }

                (tok, None)
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use std::rc::Rc;

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::parser::context::TypeToFix;
    use crate::parser::declarations::*;
    use crate::parser::expressions::*;
    use crate::parser::initializer::*;
    use crate::parser::literals::{self, *};
    use crate::parser::names::Qualified;
    use crate::parser::types::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_statement_compound_1() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             {
                   return a + b;
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Compound(Box::new(Compound {
            attributes: None,
            stmts: vec![Statement::Return(Box::new(Return {
                attributes: None,
                val: Some(node!(BinaryOp {
                    op: Operator::Add,
                    arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                })),
            }))],
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_compound_2() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             {
                 a = 1;
                 int a = 1;
                 A * b = nullptr;
                 ;
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        assert_eq!(
            stmt,
            Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![
                    Statement::Expression(Box::new(node!(BinaryOp {
                        op: Operator::Assign,
                        arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                        arg2: ExprNode::Integer(Box::new(literals::Integer {
                            value: IntLiteral::Int(1)
                        })),
                    }))),
                    Statement::Declaration(Box::new(Declaration::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: types::Identifier {
                            identifier: Some(mk_id!("a")),
                            attributes: None,
                        },
                        init: Some(Initializer::Equal(ExprNode::Integer(Box::new(
                            literals::Integer {
                                value: IntLiteral::Int(1)
                            }
                        )))),
                        bitfield_size: None,
                    })))),
                    Statement::Declaration(Box::new(Declaration::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::UD(Box::new(UserDefined {
                                name: mk_id!("A"),
                                typ: UDType::Indirect(TypeToFix::default())
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
                        identifier: types::Identifier {
                            identifier: Some(mk_id!("b")),
                            attributes: None
                        },
                        init: Some(Initializer::Equal(ExprNode::Nullptr(Box::new(Nullptr {})))),
                        bitfield_size: None,
                    })))),
                    Statement::Empty,
                ]
            }))
        );
    }

    #[test]
    fn test_statement_compound_empty() {
        let mut lexer = Lexer::<DefaultContext>::new(b"{{ ; {  ;;}} ;;}");
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Compound(Box::new(Compound {
            attributes: None,
            stmts: vec![
                Statement::Compound(Box::new(Compound {
                    attributes: None,
                    stmts: vec![
                        Statement::Empty,
                        Statement::Compound(Box::new(Compound {
                            attributes: None,
                            stmts: vec![Statement::Empty, Statement::Empty],
                        })),
                    ],
                })),
                Statement::Empty,
                Statement::Empty,
            ],
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_if() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             if constexpr (a != b) {
                   return a + b;
             } else
                   return a % b;
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::If(Box::new(If {
            attributes: None,
            constexpr: true,
            condition: node!(BinaryOp {
                op: Operator::Neq,
                arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
            }),
            then: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![Statement::Return(Box::new(Return {
                    attributes: None,
                    val: Some(node!(BinaryOp {
                        op: Operator::Add,
                        arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                        arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                    })),
                }))],
            })),
            r#else: Some(Statement::Return(Box::new(Return {
                attributes: None,
                val: Some(node!(BinaryOp {
                    op: Operator::Mod,
                    arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                })),
            }))),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_try_named() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             try {
                   /* */
             } catch (const exception & e) {
                   /* */
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Try(Box::new(Try {
            attributes: None,
            body: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
            clause: Some(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(Box::new(UserDefined {
                        name: mk_id!("exception"),
                        typ: UDType::Indirect(TypeToFix::default()),
                    })),
                    cv: CVQualifier::CONST,
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Reference,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("e")),
                    attributes: None,
                },
                init: None,
                bitfield_size: None,
            })),
            handler: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_try_unnamed() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             try {
                   /* */
             } catch (const exception&) {
                   /* */
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Try(Box::new(Try {
            attributes: None,
            body: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
            clause: Some(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::UD(Box::new(UserDefined {
                        name: mk_id!("exception"),
                        typ: UDType::Indirect(TypeToFix::default()),
                    })),
                    cv: CVQualifier::CONST,
                    pointers: Some(vec![Pointer {
                        kind: PtrKind::Reference,
                        attributes: None,
                        cv: CVQualifier::empty(),
                        ms: MSModifier::empty(),
                    }]),
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: None,
                    attributes: None,
                },
                init: None,
                bitfield_size: None,
            })),
            handler: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_try_catch_all() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             try {
                   /* */
             } catch (...) {
                   /* */
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Try(Box::new(Try {
            attributes: None,
            body: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
            clause: None,
            handler: Box::new(Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            }))),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_for_none() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             for (;;) {}
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::For(Box::new(For {
            attributes: None,
            init: None,
            condition: None,
            iteration: None,
            body: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            })),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_for_classic() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             for (int i = 0; i <= N; i++) {}
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();
        let i = Rc::new(TypeDeclarator {
            typ: Type {
                base: BaseType::Primitive(Primitive::Int),
                cv: CVQualifier::empty(),
                pointers: None,
            },
            specifier: Specifier::empty(),
            identifier: Identifier {
                identifier: Some(mk_id!("i")),
                attributes: None,
            },
            init: Some(Initializer::Equal(ExprNode::Integer(Box::new(
                literals::Integer {
                    value: IntLiteral::Int(0),
                },
            )))),
            bitfield_size: None,
        });

        let expected = Statement::For(Box::new(For {
            attributes: None,
            init: Some(DeclOrExpr::Decl(Rc::clone(&i))),
            condition: Some(node!(BinaryOp {
                op: Operator::Leq,
                arg1: ExprNode::Variable(Box::new(Variable {
                    name: mk_id!("i"),
                    decl: VarDecl::Direct(Rc::clone(&i)),
                })),
                arg2: ExprNode::Variable(Box::new(mk_var!("N"))),
            })),
            iteration: Some(node!(UnaryOp {
                op: Operator::PostInc,
                arg: ExprNode::Variable(Box::new(Variable {
                    name: mk_id!("i"),
                    decl: VarDecl::Direct(Rc::clone(&i)),
                })),
            })),
            body: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            })),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_for_range() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             for (auto& x : y.items()) {}
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::ForRange(Box::new(ForRange {
            attributes: None,
            init: None,
            decl: Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Auto,
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
                    attributes: None,
                },
                init: None,
                bitfield_size: None,
            }),
            expr: node!(CallExpr {
                callee: node!(BinaryOp {
                    op: Operator::Dot,
                    arg1: ExprNode::Variable(Box::new(mk_var!("y"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("items"))),
                }),
                params: vec![]
            }),
            body: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            })),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_for_range_init() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             for (T thing = foo(); auto& x : thing.items()) {}
             ",
        );
        let parser = StatementParser::new(&mut lexer);
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
        let thing = Rc::new(TypeDeclarator {
            typ: Type {
                base: BaseType::UD(Box::new(UserDefined {
                    name: mk_id!("T"),
                    typ: UDType::Direct(Rc::clone(&t)),
                })),
                cv: CVQualifier::empty(),
                pointers: None,
            },
            specifier: Specifier::empty(),
            identifier: Identifier {
                identifier: Some(mk_id!("thing")),
                attributes: None,
            },
            init: Some(Initializer::Equal(node!(CallExpr {
                callee: ExprNode::Variable(Box::new(mk_var!("foo"))),
                params: vec![]
            }))),
            bitfield_size: None,
        });

        context.add_type_decl(Rc::clone(&t));

        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::ForRange(Box::new(ForRange {
            attributes: None,
            init: Some(DeclOrExpr::Decl(Rc::clone(&thing))),
            decl: Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Auto,
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
                    attributes: None,
                },
                init: None,
                bitfield_size: None,
            }),
            expr: node!(CallExpr {
                callee: node!(BinaryOp {
                    op: Operator::Dot,
                    arg1: ExprNode::Variable(Box::new(Variable {
                        name: mk_id!("thing"),
                        decl: VarDecl::Direct(Rc::clone(&thing)),
                    })),
                    arg2: ExprNode::Variable(Box::new(mk_var!("items"))),
                }),
                params: vec![]
            }),
            body: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![],
            })),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_switch() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"
             switch (x) {
                 case 1:
                     break;
                 case 2:
                 case 3:
                     break;
                 default:
                     break;
             }
             ",
        );
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();

        let x = Rc::new(TypeDeclarator {
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
            init: None,
            bitfield_size: None,
        });
        context.add_type_decl(Rc::clone(&x));

        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::Switch(Box::new(Switch {
            attributes: None,
            condition: DeclOrExpr::Expr(ExprNode::Variable(Box::new(Variable {
                name: mk_id!("x"),
                decl: VarDecl::Direct(x),
            }))),
            cases: Statement::Compound(Box::new(Compound {
                attributes: None,
                stmts: vec![
                    Statement::Case(Box::new(Case {
                        attributes: None,
                        value: ExprNode::Integer(Box::new(literals::Integer {
                            value: IntLiteral::Int(1),
                        })),
                    })),
                    Statement::Break(Box::new(Break { attributes: None })),
                    Statement::Case(Box::new(Case {
                        attributes: None,
                        value: ExprNode::Integer(Box::new(literals::Integer {
                            value: IntLiteral::Int(2),
                        })),
                    })),
                    Statement::Case(Box::new(Case {
                        attributes: None,
                        value: ExprNode::Integer(Box::new(literals::Integer {
                            value: IntLiteral::Int(3),
                        })),
                    })),
                    Statement::Break(Box::new(Break { attributes: None })),
                    Statement::Default(Box::new(Default { attributes: None })),
                    Statement::Break(Box::new(Break { attributes: None })),
                ],
            })),
        }));

        assert_eq!(stmt, expected);
    }

    #[test]
    fn test_statement_while() {
        let mut lexer = Lexer::<DefaultContext>::new(b"while (0) while(0) do ; while(0);");
        let parser = StatementParser::new(&mut lexer);
        let mut context = Context::default();
        let stmt = parser.parse(None, &mut context).1.unwrap();

        let expected = Statement::While(Box::new(While {
            attributes: None,
            condition: DeclOrExpr::Expr(ExprNode::Integer(Box::new(literals::Integer {
                value: IntLiteral::Int(0),
            }))),
            body: Statement::While(Box::new(While {
                attributes: None,
                condition: DeclOrExpr::Expr(ExprNode::Integer(Box::new(literals::Integer {
                    value: IntLiteral::Int(0),
                }))),
                body: Statement::Do(Box::new(Do {
                    attributes: None,
                    body: Statement::Empty,
                    condition: ExprNode::Integer(Box::new(literals::Integer {
                        value: IntLiteral::Int(0),
                    })),
                })),
            })),
        }));

        assert_eq!(stmt, expected);
    }
}
