// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::{
    DeclHint, Declaration, DeclarationListParser, Declarations, Specifier, TypeDeclaratorParser,
};
use crate::lexer::{TLexer, Token};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::names::{Qualified, QualifiedParser};
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct NsName {
    pub inline: bool,
    pub name: String,
}

impl Dump for NsName {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, inline, name);
    }
}

impl AsRef<str> for NsName {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

pub type NsNames = Vec<NsName>;

impl Dump for NsNames {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "ns", prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Namespace {
    pub name: NsNames,
    pub body: Declarations,
}

impl Dump for Namespace {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "namespace", prefix, last, stdout, name, body);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct NamespaceAlias {
    pub name: String,
    pub alias: Qualified,
}

impl Dump for NamespaceAlias {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "namespace-alias",
            prefix,
            last,
            stdout,
            name,
            alias
        );
    }
}

struct NsNamesParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> NsNamesParser<'a, L> {
    fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    fn parse(self, _context: &mut Context) -> Result<(Option<Token>, NsNames), ParserError> {
        let mut tok = self.lexer.next_useful();
        let mut names = Vec::new();
        let mut inline = false;

        loop {
            match tok {
                Token::Inline => {
                    inline = true;
                }
                Token::Identifier(id) => {
                    names.push(NsName { inline, name: id });
                }
                Token::ColonColon => {
                    inline = false;
                }
                _ => {
                    if names.is_empty() {
                        names.push(NsName {
                            inline: false,
                            name: "".to_string(),
                        });
                    }
                    return Ok((Some(tok), names));
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}

pub struct NamespaceParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> NamespaceParser<'a, L> {
    pub(super) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Declaration>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let inline = if tok == Token::Inline {
            let tok = self.lexer.next_useful();
            if tok != Token::Namespace {
                let tdp = TypeDeclaratorParser::new(self.lexer);
                let hint = DeclHint::Specifier(Specifier::INLINE);
                let (tok, typ) = tdp.parse(Some(tok), Some(hint), true, context)?;
                let typ = typ.unwrap();
                context.add_type_decl(Rc::clone(&typ));

                return Ok((tok, Some(Declaration::Type(typ))));
            }
            true
        } else if tok != Token::Namespace {
            return Ok((Some(tok), None));
        } else {
            false
        };

        let np = NsNamesParser::new(self.lexer);
        let (tok, mut name) = np.parse(context)?;
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if inline {
            name[0].inline = true;
        }

        match tok {
            Token::LeftBrace => {
                let name_len = name.len();
                context.set_current_ns(&name);

                let dlp = DeclarationListParser::new(self.lexer);
                let (tok, body) = dlp.parse(None, context)?;

                let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
                if tok == Token::RightBrace {
                    let ns = Namespace {
                        name,
                        body: body.unwrap(),
                    };

                    if name_len != 0 {
                        context.pop_n(name_len);
                    }
                    Ok((None, Some(Declaration::Namespace(ns))))
                } else {
                    Err(ParserError::InvalidTokenInNs {
                        sp: self.lexer.span(),
                        tok,
                    })
                }
            }
            Token::Equal => {
                let qp = QualifiedParser::new(self.lexer);
                let (tok, alias) = qp.parse(None, None, context)?;

                let mut s = String::new();
                std::mem::swap(&mut s, &mut name[0].name);

                let ns = NamespaceAlias {
                    name: s,
                    alias: alias.unwrap(),
                };
                Ok((tok, Some(Declaration::NamespaceAlias(ns))))
            }
            _ => Err(ParserError::InvalidTokenInNs {
                sp: self.lexer.span(),
                tok,
            }),
        }
    }
}

#[cfg(test)]
mod tests {

    use std::cell::RefCell;

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::parser::declarations::{types, *};
    use crate::parser::names::*;
    use crate::parser::types::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_namespace_one() {
        let mut l = Lexer::<DefaultContext>::new(b"A");
        let p = NsNamesParser::new(&mut l);
        let mut context = Context::default();
        let (_, ns) = p.parse(&mut context).unwrap();

        assert_eq!(
            ns,
            vec![NsName {
                inline: false,
                name: "A".to_string(),
            }]
        );
    }

    #[test]
    fn test_namespace_multiple() {
        let mut l = Lexer::<DefaultContext>::new(b"A::inline B::C::inline D::E");
        let p = NsNamesParser::new(&mut l);
        let mut context = Context::default();
        let (_, ns) = p.parse(&mut context).unwrap();

        assert_eq!(
            ns,
            vec![
                NsName {
                    inline: false,
                    name: "A".to_string(),
                },
                NsName {
                    inline: true,
                    name: "B".to_string(),
                },
                NsName {
                    inline: false,
                    name: "C".to_string(),
                },
                NsName {
                    inline: true,
                    name: "D".to_string(),
                },
                NsName {
                    inline: false,
                    name: "E".to_string(),
                },
            ]
        );
    }

    #[test]
    fn test_namespace_body() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
namespace A {
    namespace B {
        void f();
    }
    void g();
}
        "#,
        );
        let p = DeclarationParser::new(&mut l);
        let mut context = Context::default();
        let (_, ns) = p.parse(None, None, &mut context).unwrap();
        let ns = ns.unwrap();

        assert_eq!(
            ns,
            Declaration::Namespace(Namespace {
                name: vec![NsName {
                    inline: false,
                    name: "A".to_string(),
                },],
                body: vec![
                    Declaration::Namespace(Namespace {
                        name: vec![NsName {
                            inline: false,
                            name: "B".to_string(),
                        },],
                        body: vec![Declaration::Type(Rc::new(TypeDeclarator {
                            typ: Type {
                                base: BaseType::Function(Box::new(Function {
                                    return_type: Some(Type {
                                        base: BaseType::Primitive(Primitive::Void),
                                        cv: CVQualifier::empty(),
                                        pointers: None,
                                    }),
                                    params: vec![],
                                    cv: CVQualifier::empty(),
                                    refq: RefQualifier::None,
                                    except: None,
                                    attributes: None,
                                    trailing: None,
                                    virt_specifier: VirtSpecifier::empty(),
                                    status: FunStatus::None,
                                    requires: None,
                                    ctor_init: None,
                                    body: RefCell::new(None)
                                })),
                                cv: CVQualifier::empty(),
                                pointers: None,
                            },
                            specifier: Specifier::empty(),
                            identifier: types::Identifier {
                                identifier: Some(mk_id!("f")),
                                attributes: None
                            },
                            init: None,
                            bitfield_size: None,
                        }))],
                    },),
                    Declaration::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::Function(Box::new(Function {
                                return_type: Some(Type {
                                    base: BaseType::Primitive(Primitive::Void),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                }),
                                params: vec![],
                                cv: CVQualifier::empty(),
                                refq: RefQualifier::None,
                                except: None,
                                attributes: None,
                                trailing: None,
                                virt_specifier: VirtSpecifier::empty(),
                                status: FunStatus::None,
                                requires: None,
                                ctor_init: None,
                                body: RefCell::new(None)
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: types::Identifier {
                            identifier: Some(mk_id!("g")),
                            attributes: None
                        },
                        init: None,
                        bitfield_size: None,
                    }))
                ],
            })
        );
    }

    #[test]
    fn test_namespace_alias() {
        let mut l = Lexer::<DefaultContext>::new(b"namespace A = B::C::D::E;");
        let p = DeclarationParser::new(&mut l);
        let mut context = Context::default();
        let (_, ns) = p.parse(None, None, &mut context).unwrap();
        let ns = ns.unwrap();

        assert_eq!(
            ns,
            Declaration::NamespaceAlias(NamespaceAlias {
                name: "A".to_string(),
                alias: mk_id!("B", "C", "D", "E"),
            })
        );
    }
}
