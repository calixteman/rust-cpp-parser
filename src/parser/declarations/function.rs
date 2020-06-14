// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use std::cell::RefCell;
use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::super::types::{BaseType, CVQualifier, Type};
use super::specifier::Specifier;
use super::types::{Identifier, TypeDeclarator, TypeDeclaratorParser};
use crate::lexer::extra::SavedLexer;
use crate::lexer::{TLexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{ExprNode, ExpressionParser, Parameters, ParametersParser};
use crate::parser::initializer::{Initializer, InitializerParser};
use crate::parser::names::{Name, OperatorParser, Qualified, QualifiedParser};
use crate::parser::statements::{Compound, CompoundStmtParser};
use crate::parser::{Context, ScopeKind, TypeToFix};

#[derive(Clone, Debug, PartialEq)]
pub struct Parameter {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) decl: Rc<TypeDeclarator>,
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

pub struct CtorInitializersParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> CtorInitializersParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<CtorInitializers>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Colon {
            return Ok((Some(tok), None));
        }

        let mut inits = Vec::new();
        let mut tok = Some(tok);

        loop {
            let qp = QualifiedParser::new(self.lexer);
            let (tk, name) = qp.parse(tok, None, context)?;

            let name = if let Some(name) = name {
                name
            } else {
                return Err(ParserError::InvalidCtorInit {
                    sp: self.lexer.span(),
                });
            };

            let ip = InitializerParser::new(self.lexer);
            let (tk, init) = ip.parse(tk, context)?;

            let init = if let Some(init) = init {
                init
            } else {
                return Err(ParserError::InvalidCtorInit {
                    sp: self.lexer.span(),
                });
            };

            inits.push(CtorInit { name, init });

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            if tk != Token::Comma {
                return Ok((Some(tk), Some(inits)));
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
    pub body: RefCell<Option<Compound>>,
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

pub struct ParameterListParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ParameterListParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        skip_lparen: bool,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Vec<Parameter>>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut tok = if skip_lparen {
            Some(tok)
        } else if tok != Token::LeftParen {
            return Ok((Some(tok), None));
        } else {
            None
        };

        let mut params = Vec::new();

        loop {
            let ap = AttributesParser::new(self.lexer);
            let (tk, attributes) = ap.parse(tok, context)?;

            let dp = TypeDeclaratorParser::new(self.lexer);
            let (tk, decl) = dp.parse(tk, None, true, context)?;
            let decl = if let Some(decl) = decl {
                decl
            } else {
                return Ok((None, Some(params)));
            };

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            match tk {
                Token::Comma => {
                    params.push(Parameter { attributes, decl });
                }
                Token::RightParen => {
                    params.push(Parameter { attributes, decl });
                    return Ok((None, Some(params)));
                }
                _ => {
                    return Err(ParserError::InvalidTokenInParamList {
                        sp: self.lexer.span(),
                        tok: tk,
                    });
                }
            }
            tok = None;
        }
    }
}

pub struct FunctionParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> FunctionParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        skip_lparen: bool,
        name: Option<&Qualified>,
        context: &mut Context,
    ) -> Result<
        (
            Option<Token>,
            Option<Function>,
            Option<TypeToFix>,
            Option<SavedLexer>,
        ),
        ParserError,
    > {
        let plp = ParameterListParser::new(self.lexer);
        let (tok, params) = plp.parse(tok, skip_lparen, context)?;
        let params = if let Some(params) = params {
            params
        } else {
            return Ok((tok, None, None, None));
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
        let (tok, except) = ep.parse(tok, context)?;

        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, trailing) = if tok == Token::Arrow {
            let tdp = TypeDeclaratorParser::new(self.lexer);
            let (tok, decl) = tdp.parse(None, None, false, context)?;
            (tok, decl.map(|d| Rc::try_unwrap(d).unwrap().typ))
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
            let (tok, e) = ep.parse(None, context)?;
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
                    return Err(ParserError::InvalidTokenInFuncDecl {
                        sp: self.lexer.span(),
                        tok,
                    });
                }
            }
        } else {
            (tok, FunStatus::None)
        };

        let cip = CtorInitializersParser::new(self.lexer);
        let (tok, ctor_init) = cip.parse(Some(tok), context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let (tok, body, to_fix, saved) = if tok == Token::LeftBrace {
            if context.in_class() {
                // we're in a class/struct so we must postpone the body parsing
                // to avoid to have issues due to the use of unknown members.
                let (_, saved) = self.lexer.save_until(Token::RightBrace, 1);
                (None, Some(Compound::default()), None, Some(saved))
            } else {
                context.set_current(name, ScopeKind::Function);
                for param in params.iter() {
                    context.add_type_decl(Rc::clone(&param.decl));
                }
                let cp = CompoundStmtParser::new(self.lexer);
                let (tok, body) = cp.parse(None, context)?;
                let to_fix = context.pop_n(name.map_or(1, |n| n.len()));
                (tok, body, to_fix, None)
            }
        } else {
            (Some(tok), None, None, None)
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
            body: RefCell::new(body),
        };

        Ok((tok, Some(fun), to_fix, saved))
    }
}

pub struct ExceptionParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ExceptionParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Exception>), ParserError> {
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
                    let (tok, exp) = ep.parse(None, context)?;
                    Ok((tok, Some(Exception::Noexcept(exp))))
                } else {
                    Ok((Some(tok), Some(Exception::Noexcept(None))))
                }
            }
            Token::Throw => {
                let tok = self.lexer.next_useful();
                if tok == Token::LeftParen {
                    let pp = ParametersParser::new(self.lexer, Token::RightParen);
                    let (tok, params) = pp.parse(None, None, context)?;
                    Ok((tok, Some(Exception::Throw(params))))
                } else {
                    return Err(ParserError::InvalidTokenInThrow {
                        sp: self.lexer.span(),
                        tok,
                    });
                }
            }
            _ => Ok((Some(tok), None)),
        }
    }
}

pub(crate) struct ConvOperatorDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ConvOperatorDeclaratorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        specifier: Specifier,
        name: Option<Qualified>,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<
        (
            Option<Token>,
            Option<TypeDeclarator>,
            Option<TypeToFix>,
            Option<SavedLexer>,
        ),
        ParserError,
    > {
        let (tok, name) = if name.is_none() {
            let op = OperatorParser::new(self.lexer);
            let (tok, op) = op.parse(tok, context)?;

            if let Some(op) = op {
                (
                    tok,
                    Some(Qualified {
                        names: vec![Name::Operator(Box::new(op))],
                    }),
                )
            } else {
                return Ok((tok, None, None, None));
            }
        } else {
            (tok, name)
        };

        // attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok, context)?;

        let fp = FunctionParser::new(self.lexer);
        let (tok, function, to_fix, saved) = fp.parse(tok, false, name.as_ref(), context)?;

        if let Some(function) = function {
            let typ = Type {
                base: BaseType::Function(Box::new(function)),
                cv: CVQualifier::empty(),
                pointers: None,
            };
            Ok((
                tok,
                Some(TypeDeclarator {
                    typ,
                    specifier,
                    identifier: Identifier {
                        identifier: name,
                        attributes,
                    },
                    init: None,
                    bitfield_size: None,
                }),
                to_fix,
                saved,
            ))
        } else {
            Err(ParserError::InvalidTokenInOp {
                sp: self.lexer.span(),
                tok: tok.unwrap(),
            })
        }
    }
}
