// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use termcolor::StandardStreamLock;

use super::member::{MemberParser, MemberRes, Members, Visibility};
use crate::check_semicolon;
use crate::lexer::{TLexer, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::context::{Context, ScopeKind, TypeToFix};
use crate::parser::dump::Dump;
use crate::parser::names::{Qualified, QualifiedParser};

bitflags! {
    pub struct ClassSpecifier: u8 {
        const PRIVATE = 0b1;
        const PUBLIC = 0b10;
        const PROTECTED = 0b100;
        const VIRTUAL = 0b1000;
    }
}

impl ClassSpecifier {
    pub fn from_tok(&mut self, tok: &Token) -> bool {
        match tok {
            Token::Private => {
                *self |= Self::PRIVATE;
                true
            }
            Token::Public => {
                *self |= Self::PUBLIC;
                true
            }
            Token::Protected => {
                *self |= Self::PROTECTED;
                true
            }
            Token::Virtual => {
                *self |= Self::VIRTUAL;
                true
            }
            _ => false,
        }
    }
}

impl ToString for ClassSpecifier {
    fn to_string(&self) -> String {
        let mut vec = Vec::with_capacity(2);
        if self.contains(Self::PRIVATE) {
            vec.push("private");
        }
        if self.contains(Self::PUBLIC) {
            vec.push("public");
        }
        if self.contains(Self::PROTECTED) {
            vec.push("protected");
        }
        if self.contains(Self::VIRTUAL) {
            vec.push("virtual");
        }
        vec.join(" | ")
    }
}

impl Dump for ClassSpecifier {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), Cyan, prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    Struct,
    Class,
    Union,
}

impl Kind {
    fn from_tok(tok: &Token) -> Option<Self> {
        match tok {
            Token::Struct => Some(Kind::Struct),
            Token::Class => Some(Kind::Class),
            Token::Union => Some(Kind::Union),
            _ => None,
        }
    }

    fn to_str(&self) -> &'static str {
        match self {
            Self::Struct => "struct",
            Self::Class => "class",
            Self::Union => "union",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Derived {
    pub attributes: Option<Attributes>,
    pub name: Qualified,
    pub specifier: ClassSpecifier,
}

impl Dump for Derived {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, attributes, name, specifier);
    }
}

impl Dump for Vec<Derived> {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_vec!(name, self, "der", prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Class {
    pub kind: Kind,
    pub attributes: Option<Attributes>,
    pub name: Option<Qualified>,
    pub r#final: bool,
    pub bases: Option<Vec<Derived>>,
    pub body: Option<ClassBody>,
}

impl Dump for Class {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let cname = self.kind.to_str();
        dump_obj!(self, name, cname, prefix, last, stdout, attributes, name, r#final, bases, body);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ClassBody {
    pub public: Members,
    pub protected: Members,
    pub private: Members,
}

impl Dump for ClassBody {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "", prefix, last, stdout, public, protected, private);
    }
}

struct DerivedParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> DerivedParser<'a, L> {
    fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<Token>, context: &mut Context) -> (Option<Token>, Option<Derived>) {
        // optional: attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok, context);

        // access-specifier | virtual-specifier
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut specifier = ClassSpecifier::empty();
        while specifier.from_tok(&tok) {
            tok = self.lexer.next_useful();
        }

        // class or decltype
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(Some(tok), None, context);

        let name = if let Some(name) = name {
            name
        } else {
            return (tok, None);
        };

        (
            tok,
            Some(Derived {
                attributes,
                name,
                specifier,
            }),
        )
    }
}

struct BaseClauseParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> BaseClauseParser<'a, L> {
    fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Vec<Derived>>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if tok != Token::Colon {
            return (Some(tok), None);
        }

        let mut bases = Vec::new();

        let tok = loop {
            let dp = DerivedParser::new(self.lexer);
            let (tok, derived) = dp.parse(None, context);

            if let Some(derived) = derived {
                bases.push(derived);
            } else {
                break tok;
            }

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::Comma {
                break Some(tok);
            }
        };

        if bases.is_empty() {
            (tok, None)
        } else {
            (tok, Some(bases))
        }
    }
}

pub(crate) struct ClassParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ClassParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> (Option<Token>, Option<Class>, Option<TypeToFix>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let kind = if let Some(kind) = Kind::from_tok(&tok) {
            kind
        } else {
            return (Some(tok), None, None);
        };

        // optional: attributes
        // TODO: alignas
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(None, context);

        // optional: name
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(tok, None, context);

        // optional: final
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, r#final) = if tok == Token::Final {
            (None, true)
        } else {
            (Some(tok), false)
        };

        // optional: base-clause
        let bcp = BaseClauseParser::new(self.lexer);
        let (tok, bases) = bcp.parse(tok, context);

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, body, to_fix) = if tok == Token::LeftBrace {
            context.set_current(name.as_ref(), ScopeKind::Class);
            let cbp = ClassBodyParser::new(self.lexer);
            let (tok, body) = cbp.parse(kind.clone(), context);
            let to_fix = context.pop_n(name.as_ref().map_or(1, |n| n.len()));
            (tok, Some(body), to_fix)
        } else {
            (Some(tok), None, None)
        };

        let class = Class {
            kind,
            name,
            attributes,
            r#final,
            bases,
            body,
        };

        (tok, Some(class), to_fix)
    }
}

pub struct ClassBodyParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ClassBodyParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, kind: Kind, context: &mut Context) -> (Option<Token>, ClassBody) {
        let mut body = ClassBody {
            public: Vec::new(),
            protected: Vec::new(),
            private: Vec::new(),
        };

        let mut current = match kind {
            Kind::Class => &mut body.private,
            _ => &mut body.public,
        };

        let mut tok = None;

        loop {
            let mp = MemberParser::new(self.lexer);
            let (tk, memb) = mp.parse(tok, context);

            let tk = if let Some(memb) = memb {
                match memb {
                    MemberRes::Vis(v) => {
                        match v {
                            Visibility::Public => {
                                current = &mut body.public;
                            }
                            Visibility::Protected => {
                                current = &mut body.protected;
                            }
                            Visibility::Private => {
                                current = &mut body.private;
                            }
                        }
                        tk
                    }
                    MemberRes::Decl(decl) => {
                        let tk = if decl.has_semicolon() {
                            check_semicolon!(self, tk);
                            None
                        } else {
                            tk
                        };

                        current.push(decl);
                        tk
                    }
                }
            } else {
                tk
            };

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            tok = if tk == Token::RightBrace {
                return (None, body);
            } else {
                Some(tk)
            };
        }
    }
}

#[cfg(test)]
mod tests {

    use std::rc::Rc;

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::parser::declarations::{self, *};
    use crate::parser::expressions::{self, *};
    use crate::parser::initializer::Initializer;
    use crate::parser::names::*;
    use crate::parser::statements::*;
    use crate::parser::types::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_class() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
class A : public B, protected C {
    int x;

public:
    double y;

protected:
    char * z = nullptr;

private:

    void f();

public:
    int g() {
        return this->x;
    }
}
"#,
        );
        let p = ClassParser::new(&mut l);
        let mut context = Context::default();
        let (_, c, _) = p.parse(None, &mut context);
        let c = c.unwrap();

        let expected = Class {
            kind: super::Kind::Class,
            attributes: None,
            name: Some(mk_id!("A")),
            r#final: false,
            bases: Some(vec![
                Derived {
                    attributes: None,
                    name: mk_id!("B"),
                    specifier: ClassSpecifier::PUBLIC,
                },
                Derived {
                    attributes: None,
                    name: mk_id!("C"),
                    specifier: ClassSpecifier::PROTECTED,
                },
            ]),
            body: Some(ClassBody {
                public: vec![
                    Member::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::Primitive(Primitive::Double),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: declarations::Identifier {
                            identifier: Some(mk_id!("y")),
                            attributes: None,
                        },
                        init: None,
                        bitfield_size: None,
                    })),
                    Member::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::Function(Box::new(Function {
                                return_type: Some(Type {
                                    base: BaseType::Primitive(Primitive::Int),
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
                                body: Some(Compound {
                                    attributes: None,
                                    stmts: vec![Statement::Return(Box::new(Return {
                                        attributes: None,
                                        val: Some(node!(BinaryOp {
                                            op: expressions::operator::Operator::Arrow,
                                            arg1: ExprNode::This(Box::new(This {})),
                                            arg2: ExprNode::Qualified(Box::new(mk_id!("x"))),
                                        })),
                                    }))],
                                }),
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: declarations::Identifier {
                            identifier: Some(mk_id!("g")),
                            attributes: None,
                        },
                        init: None,
                        bitfield_size: None,
                    })),
                ],
                protected: vec![Member::Type(Rc::new(TypeDeclarator {
                    typ: Type {
                        base: BaseType::Primitive(Primitive::Char),
                        cv: CVQualifier::empty(),
                        pointers: Some(vec![Pointer {
                            kind: PtrKind::Pointer,
                            attributes: None,
                            cv: CVQualifier::empty(),
                            ms: MSModifier::empty(),
                        }]),
                    },
                    specifier: Specifier::empty(),
                    identifier: declarations::Identifier {
                        identifier: Some(mk_id!("z")),
                        attributes: None,
                    },
                    init: Some(Initializer::Equal(ExprNode::Nullptr(Box::new(Nullptr {})))),
                    bitfield_size: None,
                }))],
                private: vec![
                    Member::Type(Rc::new(TypeDeclarator {
                        typ: Type {
                            base: BaseType::Primitive(Primitive::Int),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: declarations::Identifier {
                            identifier: Some(mk_id!("x")),
                            attributes: None,
                        },
                        init: None,
                        bitfield_size: None,
                    })),
                    Member::Type(Rc::new(TypeDeclarator {
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
                                body: None,
                            })),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        },
                        specifier: Specifier::empty(),
                        identifier: declarations::Identifier {
                            identifier: Some(mk_id!("f")),
                            attributes: None,
                        },
                        init: None,
                        bitfield_size: None,
                    })),
                ],
            }),
        };

        assert_eq!(c, expected);
    }
}
