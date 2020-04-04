use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

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
    pub(crate) init: (),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Parameter {
    Single(Single),
    Init(Init),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RefQualifier {
    None,
    Lvalue,
    Rvalue,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub(crate) name: String,
    pub(crate) params: Vec<Parameter>,
    pub(crate) cv: CVQualifier,
    pub(crate) rq: RefQualifier,
}

pub struct ParameterListParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    params: Vec<Parameter>,
}

impl<'a, 'b, PC: PreprocContext> ParameterListParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            params: Vec::new(),
        }
    }

    pub(super) fn parse(
        mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Vec<Parameter>>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftParen {
            return (Some(tok), None);
        }

        loop {
            let dp = DeclarationParser::new(self.lexer);
            let (tok, decl) = dp.parse(None);
            let decl = decl.unwrap();

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => {
                    self.params.push(Parameter::Single(Single {
                        ty: decl.ty,
                        decl: decl.decl,
                    }));
                }
                Token::Equal => {
                    // TODO: get an expression
                }
                Token::RightParen => {
                    self.params.push(Parameter::Single(Single {
                        ty: decl.ty,
                        decl: decl.decl,
                    }));
                    return (None, Some(self.params));
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
    cv: CVQualifier,
    refq: RefQualifier,
}

impl<'a, 'b, PC: PreprocContext> FunctionParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            cv: CVQualifier::empty(),
            refq: RefQualifier::None,
        }
    }

    pub(super) fn parse(
        mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Function>) {
        (None, None)
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
        mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<Function>) {
        // noexcept
        // noexcept(expression)
        // throw()                    (removed in C++20)
        // throw(typeid, typeid, ...)

        /*let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Noexcept => {
                    let tok = self.lexer.next_useful();
                    if tok == Token::LeftParen {
                        let ep = ExpressionParser::new(self.lexer);
                        let (tok, exp) = ep.parse(None);

                        return (Some(tok), Some(Noexcept::new(exp)));
                    } else {
                        return (Some(tok), Some(Noexcept::new(None)));
                    }
                },
                Token::Throw => {
                    let tok = self.lexer.next_useful();
                    if tok == Token::LeftParen {
                        let mut params = Vec::new();
                        loop {
                            let dp = Declaration::parser(self.lexer);
                            let (tok, decl) = dp.parse();
                            if let Some(decl) = decl {
                                params.push(decl);
                            }

                            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                            match tok.tok {
                                Token::Comma => {
                                    continue;
                                }
                                Token::RightParen => {
                                    return (None, Some(Throw::new(params)));
                                }
                                _ => {
                                    unreachable!("Invalid token in throw: {:?}", tok);
                                }
                            }
                        }
                    } else {
                        unreachable!("throw must be followed by a (");
                    }
                }
        }*/
        (None, None)
    }
}
