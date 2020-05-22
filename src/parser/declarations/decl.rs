// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::types::{DeclHint, TypeDeclarator, TypeDeclaratorParser};
use super::{
    Asm, AsmParser, Extern, ExternParser, Namespace, NamespaceAlias, NamespaceParser, StaticAssert,
    StaticAssertParser, UsingAlias, UsingDecl, UsingEnum, UsingNS, UsingParser,
};
use crate::check_semicolon;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::dump::Dump;
use crate::parser::Context;
use crate::{dump_str, dump_vec};

#[derive(Clone, Debug, PartialEq)]
pub enum Declaration {
    Type(Rc<TypeDeclarator>),
    Extern(Extern),
    Namespace(Namespace),
    NamespaceAlias(NamespaceAlias),
    StaticAssert(StaticAssert),
    Asm(Asm),
    Attributes(Attributes),
    UsingDecl(UsingDecl),
    UsingEnum(UsingEnum),
    UsingNS(UsingNS),
    UsingAlias(UsingAlias),
    Empty,
}

impl Dump for Declaration {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::Type(x) => dump!(x),
            Self::Extern(x) => dump!(x),
            Self::Namespace(x) => dump!(x),
            Self::NamespaceAlias(x) => dump!(x),
            Self::StaticAssert(x) => dump!(x),
            Self::Asm(x) => dump!(x),
            Self::Attributes(x) => dump!(x),
            Self::UsingDecl(x) => dump!(x),
            Self::UsingEnum(x) => dump!(x),
            Self::UsingNS(x) => dump!(x),
            Self::UsingAlias(x) => dump!(x),
            Self::Empty => dump_str!(name, "empty", Cyan, prefix, last, stdout),
        }
    }
}

pub type Declarations = Vec<Declaration>;

impl Dump for Declarations {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "dec", prefix, last, stdout);
    }
}

impl Declaration {
    pub(crate) fn has_semicolon(&self) -> bool {
        match self {
            Self::Type(d) => d.has_semicolon(),
            Self::Extern(e) => !e.multiple,
            Self::Namespace(_) => false,
            _ => true,
        }
    }
}

pub(crate) struct DeclarationParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        hint: Option<DeclHint>, // TODO: remove hint
        context: &mut Context,
    ) -> (Option<Token>, Option<Declaration>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::SemiColon {
            return (None, Some(Declaration::Empty));
        }
        let tok = Some(tok);

        let ep = ExternParser::new(self.lexer);
        let (tok, decl) = ep.parse(tok, context);

        if decl.is_some() {
            return (tok, decl);
        }

        let np = NamespaceParser::new(self.lexer);
        let (tok, decl) = np.parse(tok, context);

        if decl.is_some() {
            return (tok, decl);
        }

        let sap = StaticAssertParser::new(self.lexer);
        let (tok, sa) = sap.parse(tok, context);

        if let Some(sa) = sa {
            return (tok, Some(Declaration::StaticAssert(sa)));
        }

        let ap = AttributesParser::new(self.lexer);
        let (tok, mut attrs) = ap.parse(tok, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::SemiColon {
            return (None, Some(Declaration::Attributes(attrs.unwrap())));
        }
        let tok = Some(tok);

        let ap = AsmParser::new(self.lexer);
        let (tok, asm) = ap.parse(tok, context);

        if let Some(mut asm) = asm {
            asm.attributes = attrs;
            return (tok, Some(Declaration::Asm(asm)));
        }

        let up = UsingParser::new(self.lexer);
        let (tok, using) = up.parse(tok, context);

        if let Some(mut using) = using {
            if let Declaration::UsingNS(ref mut u) = using {
                std::mem::swap(&mut u.attributes, &mut attrs);
            }
            return (tok, Some(using));
        }

        let tdp = TypeDeclaratorParser::new(self.lexer);
        let (tok, decl) = tdp.parse(tok, hint, true, context);

        let decl = if let Some(decl) = decl {
            context.add_type_decl(Rc::clone(&decl));
            Some(Declaration::Type(decl))
        } else {
            None
        };

        (tok, decl)
    }
}

pub struct DeclarationListParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationListParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Declarations>) {
        let mut tok = tok;
        let mut list = Vec::new();

        loop {
            let dp = DeclarationParser::new(self.lexer);
            let (tk, decl) = dp.parse(tok, None, context);

            tok = if let Some(decl) = decl {
                let tk = if decl.has_semicolon() {
                    check_semicolon!(self, tk);
                    None
                } else {
                    tk
                };
                list.push(decl);
                tk
            } else {
                return (tk, Some(list));
            };
        }
    }
}

#[cfg(test)]
mod tests {

    /*use super::super::function::*;
    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::array::*;
    use crate::parser::attributes::Attribute;
    use crate::parser::declarations::pointer::*;
    use crate::parser::declarations::r#enum::*;
    use crate::parser::expressions::{self, *};
    use crate::parser::literals::{self, *};
    use crate::parser::names::{self, operator, Name};
    use crate::parser::types::Primitive;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_decl() {}*/
}
