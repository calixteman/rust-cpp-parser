use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExpressionParser, Node, Parameters, ParametersParser};
use crate::parser::name::Qualified;

use super::super::r#type::{CVQualifier, Type};
use super::decl::{DeclarationParser, Declarator, DeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Single {
    pub(crate) ty: Type,
    pub(crate) decl: Declarator,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Init {
    pub(crate) ty: Type,
    pub(crate) decl: Declarator,
    pub(crate) init: Node,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Parameter {
    Single(Single),
    Init(Init),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RefQualifier {
    None,
    LValue,
    RValue,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Exception {
    Noexcept(Option<Node>),
    Throw(Option<Parameters>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub(crate) identifier: Option<Qualified>,
    pub(crate) params: Vec<Parameter>,
    pub(crate) cv: CVQualifier,
    pub(crate) refq: RefQualifier,
    pub(crate) except: Option<Exception>,
    pub(crate) trailing: Option<Node>,
}

pub struct ParameterListParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ParameterListParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Vec<Parameter>>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftParen {
            return (Some(tok), None);
        }

        let mut params = Vec::new();

        loop {
            let dp = DeclarationParser::new(self.lexer);
            let (tok, decl) = dp.parse(None);
            let decl = decl.unwrap();

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => {
                    params.push(Parameter::Single(Single {
                        ty: decl.ty,
                        decl: decl.decl,
                    }));
                }
                Token::Equal => {
                    let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
                    let (tok, expr) = ep.parse(None);
                    let tok = tok.unwrap();

                    params.push(Parameter::Init(Init {
                        ty: decl.ty,
                        decl: decl.decl,
                        init: expr.unwrap(),
                    }));

                    match tok.tok {
                        Token::Comma => {}
                        Token::RightParen => {
                            return (None, Some(params));
                        }
                        _ => {
                            unreachable!("Parameter list: {:?}", tok);
                        }
                    }
                }
                Token::RightParen => {
                    params.push(Parameter::Single(Single {
                        ty: decl.ty,
                        decl: decl.decl,
                    }));
                    return (None, Some(params));
                }
                _ => {
                    unreachable!("Parameter list: {:?}", tok);
                }
            }
        }
    }
}

pub struct FunctionParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> FunctionParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Function>) {
        let plp = ParameterListParser::new(self.lexer);
        let (tok, params) = plp.parse(tok);
        let params = if let Some(params) = params {
            params
        } else {
            return (tok, None);
        };

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let mut cv = CVQualifier::empty();
        loop {
            if !cv.from_tok(&tok.tok) {
                break;
            }
            tok = self.lexer.next_useful();
        }

        let refq = match tok.tok {
            Token::And => RefQualifier::LValue,
            Token::AndAnd => RefQualifier::RValue,
            _ => RefQualifier::None,
        };

        let ep = ExceptionParser::new(self.lexer);
        let (tok, except) = ep.parse(None);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, trailing) = if tok.tok == Token::Arrow {
            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            ep.parse(None)
        } else {
            (Some(tok), None)
        };

        let fun = Function {
            identifier: None,
            params,
            cv,
            refq,
            except,
            trailing,
        };

        (tok, Some(fun))
    }
}

pub struct ExceptionParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ExceptionParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Exception>) {
        // noexcept
        // noexcept(expression)
        // throw()                    (removed in C++20)
        // throw(typeid, typeid, ...)

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok.tok {
            Token::Noexcept => {
                let tok = self.lexer.next_useful();
                if tok.tok == Token::LeftParen {
                    let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
                    let (tok, exp) = ep.parse(None);
                    return (tok, Some(Exception::Noexcept(exp)));
                } else {
                    return (Some(tok), Some(Exception::Noexcept(None)));
                }
            }
            Token::Throw => {
                let tok = self.lexer.next_useful();
                if tok.tok == Token::LeftParen {
                    let pp = ParametersParser::new(self.lexer, Token::RightParen);
                    let (tok, params) = pp.parse(None);
                    return (tok, Some(Exception::Throw(params)));
                } else {
                    unreachable!("throw must be followed by a (");
                }
            }
            _ => {
                return (Some(tok), None);
            }
        }
    }
}
