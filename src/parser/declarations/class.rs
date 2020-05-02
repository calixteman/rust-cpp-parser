// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::declarations::Declarations;
use crate::parser::expression::{ExprNode, ExpressionParser};
use crate::parser::names::{Qualified, QualifiedParser};
use crate::parser::r#type::Type;

bitflags! {
    pub struct Specifier: u8 {
        pub const PRIVATE = 0b1;
        pub const PUBLIC = 0b10;
        pub const PROTECTED = 0b100;
        pub const VIRTUAL = 0b1000;
    }
}

impl Specifier {
    pub fn from_tok(&mut self, tok: Token) {
        match tok {
            Token::Private => {
                *self |= Specifier::PRIVATE;
            }
            Token::Public => {
                *self |= Specifier::PUBLIC;
            }
            Token::Protected => {
                *self |= Specifier::PROTECTED;
            }
            Token::Virtual => {
                *self |= Specifier::VIRTUAL;
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Struct,
    Class,
    Union,
}

impl Kind {
    fn from_tok(&tok: Token) -> Option<Self> {
        match tok {
            Token::Struct => Some(Kind::Struct),
            Token::Class => Some(Kind::Class),
            Token::Union => Some(Kind::Union),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Derived {
    pub attributes: Option<Attributes>,
    pub name: Qualified,
    pub specifier: Specifier,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Class {
    pub kind: Kind,
    pub attributes: Option<Attributes>,
    pub name: Option<Qualified>,
    pub final: bool,
    pub bases: Vec<Derived>,
    pub body: Option<Declarations>,
}

struct DerivedParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DerivedParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    (fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Derived>) {
        // optional: attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        // access-specifier | virtual-specifier
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut spec = Specifier::empty();
        while spec.from_tok(&tok.tok) {
            tok = self.lexer.next_useful();
        }
        
        // class or decltype
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(Some(tok), None);

        let name = if let Some(name) = name {
            name
        } else {
            return (tok, None);
        };

        (tok, Some(Derived {
            attributes,
            name,
            specifiers,
        }))
    }
}

struct BaseClauseParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> BaseClauseParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Vec<Derived>>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok.tok != Token::Colon {
            return (Some(tok), None);
        }

        let mut bases = Vec::new();
        
        loop {
            let dp = DerivedParser::new(self.lexer);
            let (tok, derived) = dp.parse(None);

            if let Some(derived) = derived {
                bases.push(derived);
            } else {
                break;
            }

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok.tok != Token::Comma {
                break;
            }
        }

        if bases.empty() {
            (tok, None)
        } else {
            (tok, Some(bases))
        }
    }
}

struct ClassParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ClassParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Class>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let kind = if let Some(kind) = Kind::from_tok(&tok.tok) {
            kind
        } else {
            return (Some(tok), None);
        }
        
        // optional: attributes
        // TODO: alignas
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        // name
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(tok, None);

        let name = if let Some(name) = name {
            name
        } else {
            unreachable!("Invalid token in clasee definition: {:?}", tok);
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, final) = if tok.tok == Token::Final {
            (None, true)
        } else {
            (Some(tok), false)
        };

        // optional: base-clause
        let bcp = BaseClauseParser::new(self.lexer);
        let (tok, bases) = bcp.parse(tok);

        
    }
}
