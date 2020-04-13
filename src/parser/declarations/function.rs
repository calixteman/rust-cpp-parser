use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::expression::{ExprNode, ExpressionParser, Parameters, ParametersParser};
use crate::parser::name::Qualified;
use crate::parser::statement::{Compound, CompoundStmtParser};

use super::super::r#type::CVQualifier;
use super::decl::{Declaration, DeclarationParser, Declarator};

#[derive(Clone, Debug, PartialEq)]
pub struct Parameter {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) decl: Declaration,
}

#[derive(Clone, Debug, PartialEq)]
pub enum RefQualifier {
    None,
    LValue,
    RValue,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Exception {
    Noexcept(Option<ExprNode>),
    Throw(Option<Parameters>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub(crate) identifier: Option<Qualified>,
    pub(crate) ptr_decl: Option<Declarator>,
    pub(crate) id_attributes: Option<Attributes>,
    pub(crate) params: Vec<Parameter>,
    pub(crate) cv: CVQualifier,
    pub(crate) refq: RefQualifier,
    pub(crate) except: Option<Exception>,
    pub(crate) attributes: Option<Attributes>,
    pub(crate) trailing: Option<ExprNode>,
    pub(crate) body: Option<Compound>,
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
            let ap = AttributesParser::new(self.lexer);
            let (tok, attributes) = ap.parse(None);

            let dp = DeclarationParser::new(self.lexer);
            let (tok, decl) = dp.parse(tok, None);
            let decl = if let Some(decl) = decl {
                decl
            } else {
                return (None, Some(params));
            };

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => {
                    params.push(Parameter { attributes, decl });
                }
                Token::RightParen => {
                    params.push(Parameter { attributes, decl });
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

        let (tok, refq) = match tok.tok {
            Token::And => (None, RefQualifier::LValue),
            Token::AndAnd => (None, RefQualifier::RValue),
            _ => (Some(tok), RefQualifier::None),
        };

        let ep = ExceptionParser::new(self.lexer);
        let (tok, except) = ep.parse(tok);

        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, trailing) = if tok.tok == Token::Arrow {
            let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
            ep.parse(None)
        } else {
            (Some(tok), None)
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, body) = if tok.tok == Token::LeftBrace {
            let cp = CompoundStmtParser::new(self.lexer);
            cp.parse(None)
        } else {
            (Some(tok), None)
        };

        let fun = Function {
            identifier: None,
            ptr_decl: None,
            id_attributes: None,
            params,
            cv,
            refq,
            except,
            attributes,
            trailing,
            body,
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
                    (tok, Some(Exception::Noexcept(exp)))
                } else {
                    (Some(tok), Some(Exception::Noexcept(None)))
                }
            }
            Token::Throw => {
                let tok = self.lexer.next_useful();
                if tok.tok == Token::LeftParen {
                    let pp = ParametersParser::new(self.lexer, Token::RightParen);
                    let (tok, params) = pp.parse(None);
                    (tok, Some(Exception::Throw(params)))
                } else {
                    unreachable!("throw must be followed by a (");
                }
            }
            _ => (Some(tok), None),
        }
    }
}
