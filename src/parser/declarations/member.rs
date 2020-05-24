// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::bitfield::BitFieldDeclaratorParser;
use super::{StaticAssert, StaticAssertParser, UsingAlias, UsingDecl, UsingEnum, UsingParser};
use crate::lexer::{TLexer, Token};
use crate::parser::declarations::{Declaration, TypeDeclarator, TypeDeclaratorParser};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub enum Member {
    Type(Rc<TypeDeclarator>),
    StaticAssert(StaticAssert),
    UsingDecl(UsingDecl),
    UsingEnum(UsingEnum),
    UsingAlias(UsingAlias),
    Empty,
}

impl Member {
    pub(crate) fn has_semicolon(&self) -> bool {
        match self {
            Self::Type(d) => d.has_semicolon(),
            _ => true,
        }
    }
}

impl Dump for Member {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident ) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::Type(x) => dump!(x),
            Self::StaticAssert(x) => dump!(x),
            Self::UsingDecl(x) => dump!(x),
            Self::UsingEnum(x) => dump!(x),
            Self::UsingAlias(x) => dump!(x),
            Self::Empty => dump_str!(name, "empty", Cyan, prefix, last, stdout),
        }
    }
}

pub type Members = Vec<Member>;

impl Dump for Members {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "mem", prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Visibility {
    Public,
    Protected,
    Private,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(clippy::large_enum_variant)]
pub(super) enum MemberRes {
    Vis(Visibility),
    Decl(Member),
}

pub struct MemberParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> MemberParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<MemberRes>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok == Token::SemiColon {
            return Ok((None, Some(MemberRes::Decl(Member::Empty))));
        }
        let tok = Some(tok);

        let pppp = PPPParser::new(self.lexer);
        let (tok, vis) = pppp.parse(tok, context)?;

        if let Some(vis) = vis {
            return Ok((tok, Some(MemberRes::Vis(vis))));
        }

        let sap = StaticAssertParser::new(self.lexer);
        let (tok, sa) = sap.parse(tok, context)?;

        if let Some(sa) = sa {
            return Ok((tok, Some(MemberRes::Decl(Member::StaticAssert(sa)))));
        }

        let up = UsingParser::new(self.lexer);
        let (tok, using) = up.parse(tok, context)?;

        if let Some(using) = using {
            let using = match using {
                Declaration::UsingDecl(d) => Member::UsingDecl(d),
                Declaration::UsingEnum(d) => Member::UsingEnum(d),
                Declaration::UsingAlias(d) => Member::UsingAlias(d),
                _ => {
                    return Err(ParserError::InvalidTokenInClass {
                        sp: self.lexer.span(),
                        tok: tok.unwrap(),
                    });
                }
            };

            return Ok((tok, Some(MemberRes::Decl(using))));
        }

        let tdp = TypeDeclaratorParser::new(self.lexer);
        let (tok, typ) = tdp.parse(tok, None, true, context)?;

        let mut typ = if let Some(typ) = typ {
            typ
        } else {
            return Ok((tok, None));
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let tok = if tok == Token::Colon {
            // we've a bitfield
            let bfdp = BitFieldDeclaratorParser::new(self.lexer);
            let tok = bfdp.parse(None, Rc::get_mut(&mut typ).unwrap(), context)?;
            tok
        } else {
            Some(tok)
        };

        context.add_type_decl(Rc::clone(&typ));

        Ok((tok, Some(MemberRes::Decl(Member::Type(typ)))))
    }
}

struct PPPParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> PPPParser<'a, L> {
    fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    fn parse(
        self,
        tok: Option<Token>,
        _context: &mut Context,
    ) -> Result<(Option<Token>, Option<Visibility>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let visibility = match tok {
            Token::Public => Visibility::Public,
            Token::Protected => Visibility::Protected,
            Token::Private => Visibility::Private,
            _ => {
                return Ok((Some(tok), None));
            }
        };

        let tok = self.lexer.next_useful();
        if tok != Token::Colon {
            return Err(ParserError::InvalidTokenInClass {
                sp: self.lexer.span(),
                tok,
            });
        }

        Ok((None, Some(visibility)))
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::parser::declarations::{Identifier, Specifier};
    use crate::parser::expressions::*;
    use crate::parser::initializer::Initializer;
    use crate::parser::literals::*;
    use crate::parser::names::*;
    use crate::parser::types::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_member_public() {
        let mut l = Lexer::<DefaultContext>::new(b"public:");
        let p = MemberParser::new(&mut l);
        let mut context = Context::default();
        let (_, m) = p.parse(None, &mut context).unwrap();
        let v = if let MemberRes::Vis(v) = m.unwrap() {
            v
        } else {
            assert!(false);
            return;
        };

        assert_eq!(v, Visibility::Public);
    }

    #[test]
    fn test_member_bitfield() {
        let mut l = Lexer::<DefaultContext>::new(b"int x : 4");
        let p = MemberParser::new(&mut l);
        let mut context = Context::default();
        let (_, m) = p.parse(None, &mut context).unwrap();
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            Member::Type(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: None,
                bitfield_size: Some(ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                }))),
            }))
        );
    }

    #[test]
    fn test_member_bitfield_equal() {
        let mut l = Lexer::<DefaultContext>::new(b"int x : 4 = 1");
        let p = MemberParser::new(&mut l);
        let mut context = Context::default();
        let (_, m) = p.parse(None, &mut context).unwrap();
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            Member::Type(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Equal(ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(1)
                })))),
                bitfield_size: Some(ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                }))),
            }))
        );
    }

    #[test]
    fn test_member_bitfield_brace() {
        let mut l = Lexer::<DefaultContext>::new(b"int x : 4 {1}");
        let p = MemberParser::new(&mut l);
        let mut context = Context::default();
        let (_, m) = p.parse(None, &mut context).unwrap();
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            Member::Type(Rc::new(TypeDeclarator {
                typ: Type {
                    base: BaseType::Primitive(Primitive::Int),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::empty(),
                identifier: Identifier {
                    identifier: Some(mk_id!("x")),
                    attributes: None
                },
                init: Some(Initializer::Brace(vec![ExprNode::Integer(Box::new(
                    Integer {
                        value: IntLiteral::Int(1)
                    }
                )),])),
                bitfield_size: Some(ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                }))),
            }))
        );
    }
}
