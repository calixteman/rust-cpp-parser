// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::expressions::{ExprNode, ExpressionParser, Parameters, ParametersParser};
use crate::parser::initializer::{Initializer, InitializerParser};
use crate::parser::names::{Name, OperatorParser, Qualified, QualifiedParser};
use crate::parser::statements::{Compound, CompoundStmtParser};
use bitflags::bitflags;

use super::super::types::{BaseType, CVQualifier, Type};
use super::specifier::Specifier;
use super::types::{Identifier, TypeDeclarator, TypeDeclaratorParser};

use crate::parser::dump::Dump;
use crate::{bitflags_to_str, dump_obj};
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub struct Parameter {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) decl: TypeDeclarator,
}

impl Dump for Parameter {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, attributes, decl);
    }
}

impl Dump for Vec<Parameter> {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "par", prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum RefQualifier {
    None,
    LValue,
    RValue,
}

impl ToString for RefQualifier {
    fn to_string(&self) -> String {
        match self {
            Self::None => "".to_string(),
            Self::LValue => "&".to_string(),
            Self::RValue => "&&".to_string(),
        }
    }
}

impl Dump for RefQualifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Exception {
    Noexcept(Option<ExprNode>),
    Throw(Option<Parameters>),
}

impl Dump for Exception {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        match self {
            Self::Noexcept(x) => {
                let prefix = dump_start!(name, "noexcept", prefix, last, stdout);
                x.dump("expr", &prefix, true, stdout);
            }
            Self::Throw(x) => {
                let prefix = dump_start!(name, "throw", prefix, last, stdout);
                x.dump("parameters", &prefix, true, stdout);
            }
        }
    }
}

bitflags! {
    pub struct VirtSpecifier: u8 {
        const FINAL = 0b1;
        const OVERRIDE = 0b10;
    }
}

impl ToString for VirtSpecifier {
    fn to_string(&self) -> String {
        bitflags_to_str!(self, Self, FINAL, "final", OVERRIDE, "override")
    }
}

impl Dump for VirtSpecifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FunStatus {
    None,
    Pure,
    Default,
    Delete,
}

impl ToString for FunStatus {
    fn to_string(&self) -> String {
        match self {
            Self::None => "".to_string(),
            Self::Pure => "pure".to_string(),
            Self::Default => "default".to_string(),
            Self::Delete => "delete".to_string(),
        }
    }
}

impl Dump for FunStatus {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

impl VirtSpecifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Final => {
                *self |= VirtSpecifier::FINAL;
                true
            }
            Token::Override => {
                *self |= VirtSpecifier::OVERRIDE;
                true
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CtorInit {
    pub name: Qualified,
    pub init: Initializer,
}

impl Dump for CtorInit {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, name, init);
    }
}

pub type CtorInitializers = Vec<CtorInit>;

impl Dump for CtorInitializers {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "ini", prefix, last, stdout);
    }
}

pub struct CtorInitializersParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> CtorInitializersParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<CtorInitializers>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Colon {
            return (Some(tok), None);
        }

        let mut inits = Vec::new();
        let mut tok = Some(tok);

        loop {
            let qp = QualifiedParser::new(self.lexer);
            let (tk, name) = qp.parse(tok, None);

            let name = if let Some(name) = name {
                name
            } else {
                unreachable!("Invalid ctor initializer: {:?}", tk);
            };

            let ip = InitializerParser::new(self.lexer);
            let (tk, init) = ip.parse(tk);

            let init = if let Some(init) = init {
                init
            } else {
                unreachable!("Invalid ctor initializer: {:?}", tk);
            };

            inits.push(CtorInit { name, init });

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            if tk != Token::Comma {
                return (Some(tk), Some(inits));
            }
            tok = Some(tk);
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    pub return_type: Option<Type>,
    pub params: Vec<Parameter>,
    pub cv: CVQualifier,
    pub refq: RefQualifier,
    pub except: Option<Exception>,
    pub attributes: Option<Attributes>,
    pub trailing: Option<Type>,
    pub virt_specifier: VirtSpecifier,
    pub status: FunStatus,
    pub requires: Option<ExprNode>,
    pub ctor_init: Option<CtorInitializers>,
    pub body: Option<Compound>,
}

impl Dump for Function {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "function",
            prefix,
            last,
            stdout,
            return_type,
            params,
            cv,
            refq,
            except,
            attributes,
            trailing,
            virt_specifier,
            status,
            requires,
            ctor_init,
            body
        );
    }
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
        tok: Option<Token>,
        skip_lparen: bool,
    ) -> (Option<Token>, Option<Vec<Parameter>>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut tok = if skip_lparen {
            Some(tok)
        } else {
            if tok != Token::LeftParen {
                return (Some(tok), None);
            }
            None
        };

        let mut params = Vec::new();

        loop {
            let ap = AttributesParser::new(self.lexer);
            let (tk, attributes) = ap.parse(tok);

            let dp = TypeDeclaratorParser::new(self.lexer);
            let (tk, decl) = dp.parse(tk, None, true);
            let decl = if let Some(decl) = decl {
                decl
            } else {
                return (None, Some(params));
            };

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            match tk {
                Token::Comma => {
                    params.push(Parameter { attributes, decl });
                }
                Token::RightParen => {
                    params.push(Parameter { attributes, decl });
                    return (None, Some(params));
                }
                _ => {
                    unreachable!("Parameter list: {:?}", tk);
                }
            }
            tok = None;
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
        tok: Option<Token>,
        skip_lparen: bool,
    ) -> (Option<Token>, Option<Function>) {
        let plp = ParameterListParser::new(self.lexer);
        let (tok, params) = plp.parse(tok, skip_lparen);
        let params = if let Some(params) = params {
            params
        } else {
            return (tok, None);
        };

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let mut cv = CVQualifier::empty();
        loop {
            if !cv.from_tok(&tok) {
                break;
            }
            tok = self.lexer.next_useful();
        }

        let (tok, refq) = match tok {
            Token::And => (None, RefQualifier::LValue),
            Token::AndAnd => (None, RefQualifier::RValue),
            _ => (Some(tok), RefQualifier::None),
        };

        let ep = ExceptionParser::new(self.lexer);
        let (tok, except) = ep.parse(tok);

        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, trailing) = if tok == Token::Arrow {
            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) = tdp.parse(None, None, false);
            (tok, decl.map(|d| d.typ))
        } else {
            (Some(tok), None)
        };

        let mut virt_specifier = VirtSpecifier::empty();
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        while virt_specifier.from_tok(&tok) {
            tok = self.lexer.next_useful();
        }

        let (tok, requires) = if tok == Token::Requires {
            let mut ep = ExpressionParser::new(self.lexer, Token::Eof);
            let (tok, e) = ep.parse(None);
            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            (tok, e)
        } else {
            (tok, None)
        };

        let (tok, status) = if tok == Token::Equal {
            let tok = self.lexer.next_useful();
            match tok {
                Token::Default => (self.lexer.next_useful(), FunStatus::Default),
                Token::Delete => (self.lexer.next_useful(), FunStatus::Delete),
                Token::LiteralInt(0) => (self.lexer.next_useful(), FunStatus::Pure),
                _ => {
                    unreachable!("Invalid token in function declaration: {:?}", tok);
                }
            }
        } else {
            (tok, FunStatus::None)
        };

        let cip = CtorInitializersParser::new(self.lexer);
        let (tok, ctor_init) = cip.parse(Some(tok));

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, body) = if tok == Token::LeftBrace {
            let cp = CompoundStmtParser::new(self.lexer);
            cp.parse(None)
        } else {
            (Some(tok), None)
        };

        let fun = Function {
            return_type: None,
            params,
            cv,
            refq,
            except,
            attributes,
            trailing,
            virt_specifier,
            status,
            requires,
            ctor_init,
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

    pub(super) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<Exception>) {
        // noexcept
        // noexcept(expression)
        // throw()                    (removed in C++20)
        // throw(typeid, typeid, ...)

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok {
            Token::Noexcept => {
                let tok = self.lexer.next_useful();
                if tok == Token::LeftParen {
                    let mut ep = ExpressionParser::new(self.lexer, Token::RightParen);
                    let (tok, exp) = ep.parse(None);
                    (tok, Some(Exception::Noexcept(exp)))
                } else {
                    (Some(tok), Some(Exception::Noexcept(None)))
                }
            }
            Token::Throw => {
                let tok = self.lexer.next_useful();
                if tok == Token::LeftParen {
                    let pp = ParametersParser::new(self.lexer, Token::RightParen);
                    let (tok, params) = pp.parse(None, None);
                    (tok, Some(Exception::Throw(params)))
                } else {
                    unreachable!("throw must be followed by a (");
                }
            }
            _ => (Some(tok), None),
        }
    }
}

pub(crate) struct ConvOperatorDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ConvOperatorDeclaratorParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        specifier: Specifier,
        name: Option<Qualified>,
        tok: Option<Token>,
    ) -> (Option<Token>, Option<TypeDeclarator>) {
        let (tok, name) = if name.is_none() {
            let op = OperatorParser::new(self.lexer);
            let (tok, op) = op.parse(tok);

            if let Some(op) = op {
                (
                    tok,
                    Some(Qualified {
                        names: vec![Name::Operator(Box::new(op))],
                    }),
                )
            } else {
                return (tok, None);
            }
        } else {
            (tok, name)
        };

        // attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        let fp = FunctionParser::new(self.lexer);
        let (tok, function) = fp.parse(tok, false);

        if let Some(function) = function {
            let typ = Type {
                base: BaseType::Function(Box::new(function)),
                cv: CVQualifier::empty(),
                pointers: None,
            };
            (
                tok,
                Some(TypeDeclarator {
                    typ,
                    specifier,
                    identifier: Identifier {
                        identifier: name,
                        attributes,
                    },
                    init: None,
                }),
            )
        } else {
            unreachable!("Invalid token in operator name: {:?}", tok);
        }
    }
}
