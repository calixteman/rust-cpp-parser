// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{DeclarationList, DeclarationListParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::declarations::{DeclHint, DeclarationParser, Specifier};
use crate::parser::statements::Statement;
use crate::{check_semicolon, check_semicolon_or_not};

#[derive(Clone, Debug, PartialEq)]
pub enum Linkage {
    Single(Statement),
    Multiple(DeclarationList),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Extern {
    pub(crate) language: String,
    pub(crate) linkage: Linkage,
}

pub(super) enum EPRes {
    Extern(Extern),
    Declaration(Statement),
}

pub struct ExternParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ExternParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<EPRes>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::Extern {
            return (Some(tok), None);
        }

        let tok = self.lexer.next_useful();

        if let Token::LiteralString(language) = tok.tok {
            let tok = self.lexer.next_useful();
            match tok.tok {
                Token::LeftBrace => {
                    let dlp = DeclarationListParser::new(self.lexer);
                    let (tok, list) = dlp.parse(None);

                    (
                        tok,
                        Some(EPRes::Extern(Extern {
                            language,
                            linkage: Linkage::Multiple(list.unwrap()),
                        })),
                    )
                }
                _ => {
                    let dp = DeclarationParser::new(self.lexer);
                    let (tok, decl) = dp.parse(Some(tok), None);
                    let (_, decl): (Option<LocToken>, _) = check_semicolon_or_not!(self, tok, decl);
                    (
                        None,
                        Some(EPRes::Extern(Extern {
                            language,
                            linkage: Linkage::Single(decl.unwrap()),
                        })),
                    )
                }
            }
        } else {
            let dp = DeclarationParser::new(self.lexer);
            let hint = DeclHint::Specifier(Specifier::EXTERN);
            let (tok, decl) = dp.parse(Some(tok), Some(hint));
            let (tok, decl) = check_semicolon_or_not!(self, tok, decl);

            (tok, Some(EPRes::Declaration(decl.unwrap())))
        }
    }
}
