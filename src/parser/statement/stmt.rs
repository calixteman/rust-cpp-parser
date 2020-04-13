use super::{
    Case, CaseStmtParser, Compound, CompoundStmtParser, Default, DefaultStmtParser, Do,
    DoStmtParser, Goto, GotoStmtParser, If, IfStmtParser, Return, ReturnStmtParser, Switch,
    SwitchStmtParser, While, WhileStmtParser,
};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::decl::{DeclHint, Declaration, DeclarationParser, DeclaratorParser};
use crate::parser::expression::{ExprNode, ExpressionParser};
use crate::parser::name::QualifiedParser;

#[derive(Clone, Debug, PartialEq)]
pub struct Break {
    pub(crate) attributes: Option<Attributes>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Continue {
    pub(crate) attributes: Option<Attributes>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Compound(Compound),
    Return(Return),
    If(If),
    Switch(Switch),
    Case(Case),
    Default(Default),
    Do(Do),
    While(While),
    Continue(Continue),
    Break(Break),
    Goto(Goto),
    Declaration(Declaration),
    Expression(ExprNode),
    Empty,
}

#[macro_export]
macro_rules! check_semicolon {
    ( $self:expr, $tok:expr ) => {
        let tok = $tok.unwrap_or_else(|| $self.lexer.next_useful());
        if tok.tok != Token::SemiColon {
            unreachable!("Invalid token in statement: {:?}", tok);
        }
    };
}

#[macro_export]
macro_rules! check_semicolon_or_not {
    ( $self:expr, $tok:expr, $decl: expr ) => {
        if let Some(decl) = $decl {
            let tok = if let crate::parser::decl::Declarator::Function(_) = decl.decl {
                $tok
            } else {
                check_semicolon!($self, $tok);
                None
            };
            (
                tok,
                Some(crate::parser::statement::Statement::Declaration(decl)),
            )
        } else {
            ($tok, None)
        }
    };
}

pub struct StatementParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> StatementParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Statement>) {
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok.tok {
            Token::Return => {
                let rp = ReturnStmtParser::new(self.lexer);
                let (tok, ret) = rp.parse(attributes);
                check_semicolon!(self, tok);
                return (None, Some(Statement::Return(ret.unwrap())));
            }
            Token::LeftBrace => {
                let cp = CompoundStmtParser::new(self.lexer);
                let (_, compound) = cp.parse(attributes);
                return (None, Some(Statement::Compound(compound.unwrap())));
            }
            Token::If => {
                let ip = IfStmtParser::new(self.lexer);
                let (tok, ifs) = ip.parse(attributes);
                return (tok, Some(Statement::If(ifs.unwrap())));
            }
            Token::Switch => {
                let sp = SwitchStmtParser::new(self.lexer);
                let (tok, switch) = sp.parse(attributes);
                return (tok, Some(Statement::Switch(switch.unwrap())));
            }
            Token::While => {
                let wp = WhileStmtParser::new(self.lexer);
                let (tok, wh) = wp.parse(attributes);
                return (tok, Some(Statement::While(wh.unwrap())));
            }
            Token::Do => {
                let dp = DoStmtParser::new(self.lexer);
                let (tok, d) = dp.parse(attributes);
                return (tok, Some(Statement::Do(d.unwrap())));
            }
            Token::For => {}
            Token::Break => {
                check_semicolon!(self, None);
                return (None, Some(Statement::Break(Break { attributes })));
            }
            Token::Continue => {
                check_semicolon!(self, None);
                return (None, Some(Statement::Continue(Continue { attributes })));
            }
            Token::Goto => {
                let gp = GotoStmtParser::new(self.lexer);
                let (tok, goto) = gp.parse(attributes);
                check_semicolon!(self, tok);
                return (None, Some(Statement::Goto(goto.unwrap())));
            }
            Token::Try => {}
            Token::Case => {
                let cp = CaseStmtParser::new(self.lexer);
                let (tok, case) = cp.parse(attributes);
                return (tok, Some(Statement::Case(case.unwrap())));
            }
            Token::Default => {
                let dp = DefaultStmtParser::new(self.lexer);
                let (tok, default) = dp.parse(attributes);
                return (tok, Some(Statement::Default(default.unwrap())));
            }
            Token::SemiColon => {
                return (None, Some(Statement::Empty));
            }
            Token::Identifier(id) => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, name) = qp.parse(None, Some(id));

                let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                let (tok, stmt) = if DeclaratorParser::<PC>::is_decl_part(&tok.tok) {
                    let dp = DeclarationParser::new(self.lexer);
                    let hint = DeclHint::with_name(name);
                    let (tok, decl) = dp.parse(Some(tok), Some(hint));

                    (tok, Some(Statement::Declaration(decl.unwrap())))
                } else {
                    let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                    let (tok, expr) = ep.parse_with_id(Some(tok), name.unwrap());

                    (tok, Some(Statement::Expression(expr.unwrap())))
                };

                check_semicolon!(self, tok);
                return (None, stmt);
            }
            _ => {
                let dp = DeclarationParser::new(self.lexer);
                let (tok, decl) = dp.parse(Some(tok), None);
                let (tok, decl) = check_semicolon_or_not!(self, tok, decl);

                if decl.is_some() {
                    return (tok, decl);
                }

                let mut ep = ExpressionParser::new(self.lexer, Token::SemiColon);
                let (tok, expr) = ep.parse(tok);

                if let Some(expr) = expr {
                    check_semicolon!(self, tok);
                    return (None, Some(Statement::Expression(expr)));
                }

                return (tok, None);
            }
        }

        (Some(tok), None)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::declarations::*;
    use crate::parser::expression::*;
    use crate::parser::initializer::*;
    use crate::parser::literals::{self, *};
    use crate::parser::name::*;
    use crate::parser::r#type::*;
    use pretty_assertions::{assert_eq, assert_ne};

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
        let stmt = parser.parse(None).1.unwrap();

        let expected = Statement::Compound(Compound {
            attributes: None,
            stmts: vec![Statement::Return(Return {
                attributes: None,
                val: Some(node!(BinaryOp {
                    op: Operator::Add,
                    arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                    arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                })),
            })],
        });

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
        let stmt = parser.parse(None).1.unwrap();

        assert_eq!(
            stmt,
            Statement::Compound(Compound {
                attributes: None,
                stmts: vec![
                    Statement::Expression(node!(BinaryOp {
                        op: Operator::Assign,
                        arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                        arg2: ExprNode::Integer(Box::new(literals::Integer {
                            value: IntLiteral::Int(1)
                        })),
                    })),
                    Statement::Declaration(Declaration {
                        ty: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty()
                        },
                        spec: Specifier::empty(),
                        decl: Declarator::Identifier(decl::Identifier {
                            identifier: mk_id!("a"),
                            attributes: None,
                        }),
                        init: Some(Initializer::Equal(ExprNode::Integer(Box::new(
                            literals::Integer {
                                value: IntLiteral::Int(1)
                            }
                        )))),
                    }),
                    Statement::Declaration(Declaration {
                        ty: Type {
                            base: BaseType::UD(mk_id!("A"),),
                            cv: CVQualifier::empty()
                        },
                        spec: Specifier::empty(),
                        decl: Declarator::Pointer(Pointer {
                            decl: Box::new(Declarator::Identifier(decl::Identifier {
                                identifier: mk_id!("b"),
                                attributes: None
                            })),
                            attributes: None,
                            cv: CVQualifier::empty(),
                        }),
                        init: Some(Initializer::Equal(ExprNode::Nullptr(Box::new(
                            literals::Nullptr {}
                        ))))
                    }),
                    Statement::Empty,
                ]
            })
        );
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
        let stmt = parser.parse(None).1.unwrap();

        let expected = Statement::If(If {
            attributes: None,
            constexpr: true,
            condition: node!(BinaryOp {
                op: Operator::Neq,
                arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
            }),
            then: Box::new(Statement::Compound(Compound {
                attributes: None,
                stmts: vec![Statement::Return(Return {
                    attributes: None,
                    val: Some(node!(BinaryOp {
                        op: Operator::Add,
                        arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                        arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                    })),
                })],
            })),
            r#else: Some(Box::new(Statement::Return(Return {
                attributes: None,
                val: Some(node!(BinaryOp {
                    op: Operator::Mod,
                    arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                    arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                })),
            }))),
        });

        assert_eq!(stmt, expected);
    }
}
