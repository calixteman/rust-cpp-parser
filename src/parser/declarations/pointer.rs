// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use termcolor::StandardStreamLock;

use super::super::types::CVQualifier;
use super::specifier::Specifier;
use super::types::{NoPtrDeclaratorParser, TypeDeclarator};
use crate::lexer::{TLexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::types::{BaseType, Type};
use crate::parser::Context;

bitflags! {
    pub struct MSModifier: u8 {
        const RESTRICT = 0b1;
        const UPTR = 0b10;
        const SPTR = 0b100;
        const UNALIGNED = 0b1000;
    }
}

impl ToString for MSModifier {
    fn to_string(&self) -> String {
        let mut vec = Vec::with_capacity(1);
        if self.contains(Self::RESTRICT) {
            vec.push("__restrict");
        }
        if self.contains(Self::UPTR) {
            vec.push("__uptr");
        }
        if self.contains(Self::SPTR) {
            vec.push("__sptr");
        }
        if self.contains(Self::UNALIGNED) {
            vec.push("__unaligned");
        }
        vec.join(" | ")
    }
}

impl Dump for MSModifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

impl MSModifier {
    pub(crate) fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::MSRestrict => {
                *self |= Self::RESTRICT;
                true
            }
            Token::MSUptr => {
                *self |= Self::UPTR;
                true
            }
            Token::MSSptr => {
                *self |= Self::SPTR;
                true
            }
            Token::MSUnaligned | Token::MS1Unaligned => {
                *self |= Self::UNALIGNED;
                true
            }
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum PtrKind {
    Pointer,
    Reference,
    RValue,
}

impl ToString for PtrKind {
    fn to_string(&self) -> String {
        match self {
            Self::Pointer => "*".to_string(),
            Self::Reference => "&".to_string(),
            Self::RValue => "&&".to_string(),
        }
    }
}

impl Dump for PtrKind {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

impl PtrKind {
    pub(crate) fn from_tok(tok: &Token) -> Option<Self> {
        match tok {
            Token::Star => Some(PtrKind::Pointer),
            Token::And => Some(PtrKind::Reference),
            Token::AndAnd => Some(PtrKind::RValue),
            _ => None,
        }
    }

    pub(crate) fn is_ptr(tok: &Token) -> bool {
        match tok {
            Token::Star | Token::And | Token::AndAnd => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub struct Pointer {
    pub kind: PtrKind,
    pub attributes: Option<Attributes>,
    pub cv: CVQualifier,
    pub ms: MSModifier,
}

impl Dump for Pointer {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, kind, attributes, cv, ms);
    }
}

pub type Pointers = Vec<Pointer>;

impl Dump for Pointers {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "ptr", prefix, last, stdout);
    }
}

pub struct PointerDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> PointerDeclaratorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        hint: Option<PtrKind>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Pointers>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut ptrs = Vec::new();
        let mut kind = if let Some(hint) = hint {
            hint
        } else {
            let kind = PtrKind::from_tok(&tok);
            if let Some(kind) = kind {
                kind
            } else {
                return Ok((Some(tok), None));
            }
        };

        let tok = loop {
            let ap = AttributesParser::new(self.lexer);
            let (tok, attributes) = ap.parse(None, context)?;
            let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

            let mut cv = CVQualifier::empty();
            let mut ms = MSModifier::empty();

            while cv.from_tok(&tok) || ms.from_tok(&tok) {
                tok = self.lexer.next_useful();
            }

            ptrs.push(Pointer {
                kind,
                attributes,
                cv,
                ms,
            });

            kind = if let Some(kind) = PtrKind::from_tok(&tok) {
                kind
            } else {
                break tok;
            };
        };

        Ok((Some(tok), Some(ptrs)))
    }
}

pub struct ParenPointerDeclaratorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ParenPointerDeclaratorParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, (Option<TypeDeclarator>, bool)), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::LeftParen {
            return Ok((Some(tok), (None, false)));
        }

        // The previous token was a parenthesis
        // so we can have some params (function type, e.g. int * (int, int)))
        // or a function/array pointer
        let pdp = PointerDeclaratorParser::new(self.lexer);
        let (tok, pointers) = pdp.parse(None, None, context)?;

        if pointers.is_some() {
            let npdp = NoPtrDeclaratorParser::new(self.lexer);
            let typ = Type {
                base: BaseType::None,
                cv: CVQualifier::empty(),
                pointers,
            };
            let (tok, decl, _) = npdp.parse(tok, typ, Specifier::empty(), false, false, context)?;

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                return Err(ParserError::InvalidTokenInPointer {
                    sp: self.lexer.span(),
                    tok,
                });
            }

            Ok((None, (decl, false)))
        } else {
            // we've function params
            Ok((tok, (None, true)))
        }
    }
}
