// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::bitfield::{BitFieldDeclarator, BitFieldDeclaratorParser};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::declarations::{TypeDeclarator, TypeDeclaratorParser};

#[derive(Clone, Debug, PartialEq)]
pub enum MemberDeclarator {
    BitField(BitFieldDeclarator),
    Type(TypeDeclarator),
}

impl MemberDeclarator {
    pub(crate) fn has_semicolon(&self) -> bool {
        if let MemberDeclarator::Type(decl) = &self {
            decl.has_semicolon()
        } else {
            true
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Visibility {
    Public,
    Protected,
    Private,
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum MemberRes {
    Vis(Visibility),
    Decl(MemberDeclarator),
}

pub struct MemberDeclaratorParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> MemberDeclaratorParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<MemberRes>) {
        let pppp = PPPParser::new(self.lexer);
        let (tok, vis) = pppp.parse(tok);

        if let Some(vis) = vis {
            return (tok, Some(MemberRes::Vis(vis)));
        }

        let tdp = TypeDeclaratorParser::new(self.lexer);
        let (tok, typ) = tdp.parse(tok, None);

        let typ = if let Some(typ) = typ {
            typ
        } else {
            return (tok, None);
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, member) = if tok.tok == Token::Colon {
            // we've a bitfield
            let bfdp = BitFieldDeclaratorParser::new(self.lexer);
            let (tok, bitfield) = bfdp.parse(None, typ);
            (tok, MemberDeclarator::BitField(bitfield.unwrap()))
        } else {
            (Some(tok), MemberDeclarator::Type(typ))
        };

        (tok, Some(MemberRes::Decl(member)))
    }
}

struct PPPParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> PPPParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Visibility>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let visibility = match tok.tok {
            Token::Public => Visibility::Public,
            Token::Protected => Visibility::Protected,
            Token::Private => Visibility::Private,
            _ => {
                return (Some(tok), None);
            }
        };

        let tok = self.lexer.next_useful();
        if tok.tok != Token::Colon {
            unreachable!("Invalid token {:?}", tok);
        }

        (None, Some(visibility))
    }
}

/*pub struct Members {
    pub(crate) public: Vec<>,
    pub(crate) protected: Vec<>,
    pub(crate) private: Vec<>,
}

pub(super) struct MembersParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> MembersParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Derived>) {
        (None, None)
    }
}
*/

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::declarations::{Identifier, Specifier};
    use crate::parser::expression::*;
    use crate::parser::initializer::Initializer;
    use crate::parser::literals::*;
    use crate::parser::names::*;
    use crate::parser::r#type::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_member_public() {
        let mut l = Lexer::<DefaultContext>::new(b"public:");
        let p = MemberDeclaratorParser::new(&mut l);
        let (_, m) = p.parse(None);
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
        let p = MemberDeclaratorParser::new(&mut l);
        let (_, m) = p.parse(None);
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            MemberDeclarator::BitField(BitFieldDeclarator {
                typ: TypeDeclarator {
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
                },
                size: ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                })),
            })
        );
    }

    #[test]
    fn test_member_bitfield_equal() {
        let mut l = Lexer::<DefaultContext>::new(b"int x : 4 = 1");
        let p = MemberDeclaratorParser::new(&mut l);
        let (_, m) = p.parse(None);
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            MemberDeclarator::BitField(BitFieldDeclarator {
                typ: TypeDeclarator {
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
                },
                size: ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                })),
            })
        );
    }

    #[test]
    fn test_member_bitfield_brace() {
        let mut l = Lexer::<DefaultContext>::new(b"int x : 4 {1}");
        let p = MemberDeclaratorParser::new(&mut l);
        let (_, m) = p.parse(None);
        let d = if let MemberRes::Decl(d) = m.unwrap() {
            d
        } else {
            assert!(false);
            return;
        };

        assert_eq!(
            d,
            MemberDeclarator::BitField(BitFieldDeclarator {
                typ: TypeDeclarator {
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
                    init: Some(Initializer::Brace(vec![Some(ExprNode::Integer(Box::new(
                        Integer {
                            value: IntLiteral::Int(1)
                        }
                    ))),]))
                },
                size: ExprNode::Integer(Box::new(Integer {
                    value: IntLiteral::Int(4)
                })),
            })
        );
    }
}
