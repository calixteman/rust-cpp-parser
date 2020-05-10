// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::decl::Declaration;
use super::types::{TypeDeclarator, TypeDeclaratorParser};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::names::{Qualified, QualifiedParser};

use crate::parser::dump::Dump;
use crate::{dump_obj, dump_vec};
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub struct UsingDecl {
    pub names: Names,
    pub ellipsis: bool,
}

impl Dump for UsingDecl {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "using", prefix, last, stdout, names, ellipsis);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Name {
    pub name: Qualified,
    pub typename: bool,
}

impl Dump for Name {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, name, typename);
    }
}

pub type Names = Vec<Name>;

impl Dump for Names {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "nam", prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UsingEnum {
    pub name: Qualified,
}

impl Dump for UsingEnum {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "using-enum", prefix, last, stdout, name);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UsingNS {
    pub name: Qualified,
    pub attributes: Option<Attributes>,
}

impl Dump for UsingNS {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "using-namespace",
            prefix,
            last,
            stdout,
            name,
            attributes
        );
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UsingAlias {
    pub name: String,
    pub typ: TypeDeclarator,
    pub attributes: Option<Attributes>,
}

impl Dump for UsingAlias {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "using-alias",
            prefix,
            last,
            stdout,
            name,
            typ,
            attributes
        );
    }
}

pub(super) struct UsingParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> UsingParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<Declaration>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Using {
            return (Some(tok), None);
        }

        let tok = self.lexer.next_useful();
        if tok == Token::Enum {
            let qp = QualifiedParser::new(self.lexer);
            let (tok, name) = qp.parse(None, None);

            if let Some(name) = name {
                return (tok, Some(Declaration::UsingEnum(UsingEnum { name })));
            } else {
                unreachable!("Invalid token in using enum declaration: {:?}", tok)
            };
        }

        if tok == Token::Namespace {
            let qp = QualifiedParser::new(self.lexer);
            let (tok, name) = qp.parse(None, None);

            if let Some(name) = name {
                return (
                    tok,
                    Some(Declaration::UsingNS(UsingNS {
                        name,
                        attributes: None,
                    })),
                );
            } else {
                unreachable!("Invalid token in using enum declaration: {:?}", tok)
            };
        }

        let mut names = Vec::new();
        let mut tok = tok;

        loop {
            let (tk, typename) = if tok == Token::Typename {
                (self.lexer.next_useful(), true)
            } else {
                (tok, false)
            };

            let qp = QualifiedParser::new(self.lexer);
            let (tk, name) = qp.parse(Some(tk), None);

            let name = if let Some(name) = name {
                name
            } else {
                unreachable!("Invalid token in using declaration: {:?}", tk)
            };

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            match tk {
                Token::Comma => {
                    names.push(Name { name, typename });
                    tok = self.lexer.next_useful();
                }
                Token::Ellipsis => {
                    names.push(Name { name, typename });
                    return (
                        None,
                        Some(Declaration::UsingDecl(UsingDecl {
                            names,
                            ellipsis: true,
                        })),
                    );
                }
                Token::DoubleLeftBrack => {
                    let ap = AttributesParser::new(self.lexer);
                    let (tok, attrs) = ap.parse(Some(tk));
                    let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

                    if tok != Token::Equal {
                        unreachable!("Invalid token in alias declaration: {:?}", tok)
                    }

                    let tdp = TypeDeclaratorParser::new(self.lexer);
                    let (tok, typ) = tdp.parse(None, None, false);
                    let name = name.get_first_name();

                    return (
                        tok,
                        Some(Declaration::UsingAlias(UsingAlias {
                            name,
                            typ: typ.unwrap(),
                            attributes: attrs,
                        })),
                    );
                }
                Token::Equal => {
                    let tdp = TypeDeclaratorParser::new(self.lexer);
                    let (tok, typ) = tdp.parse(None, None, false);
                    let name = name.get_first_name();

                    return (
                        tok,
                        Some(Declaration::UsingAlias(UsingAlias {
                            name,
                            typ: typ.unwrap(),
                            attributes: None,
                        })),
                    );
                }
                _ => {
                    names.push(Name { name, typename });
                    return (
                        Some(tk),
                        Some(Declaration::UsingDecl(UsingDecl {
                            names,
                            ellipsis: false,
                        })),
                    );
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::names::Qualified;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_using_one() {
        let mut l = Lexer::<DefaultContext>::new(b"using A::B");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingDecl(UsingDecl {
                names: vec![Name {
                    name: mk_id!("A", "B"),
                    typename: false,
                }],
                ellipsis: false,
            })
        );
    }

    #[test]
    fn test_using_typename_one() {
        let mut l = Lexer::<DefaultContext>::new(b"using typename A::B");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingDecl(UsingDecl {
                names: vec![Name {
                    name: mk_id!("A", "B"),
                    typename: true,
                }],
                ellipsis: false,
            })
        );
    }

    #[test]
    fn test_using_several() {
        let mut l = Lexer::<DefaultContext>::new(b"using A::B, typename C, D::E");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingDecl(UsingDecl {
                names: vec![
                    Name {
                        name: mk_id!("A", "B"),
                        typename: false,
                    },
                    Name {
                        name: mk_id!("C"),
                        typename: true,
                    },
                    Name {
                        name: mk_id!("D", "E"),
                        typename: false,
                    },
                ],
                ellipsis: false,
            })
        );
    }

    #[test]
    fn test_using_ellipsis() {
        let mut l = Lexer::<DefaultContext>::new(b"using A::B...");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingDecl(UsingDecl {
                names: vec![Name {
                    name: mk_id!("A", "B"),
                    typename: false,
                }],
                ellipsis: true,
            })
        );
    }

    #[test]
    fn test_using_enum() {
        let mut l = Lexer::<DefaultContext>::new(b"using enum A::B");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingEnum(UsingEnum {
                name: mk_id!("A", "B"),
            })
        );
    }

    #[test]
    fn test_using_namespace() {
        let mut l = Lexer::<DefaultContext>::new(b"using namespace A::B");
        let p = UsingParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            Declaration::UsingNS(UsingNS {
                name: mk_id!("A", "B"),
                attributes: None,
            })
        );
    }
}
