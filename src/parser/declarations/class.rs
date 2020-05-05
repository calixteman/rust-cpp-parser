// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::member::{MemberParser, MemberRes, Members, Visibility};
use crate::check_semicolon;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::names::{Qualified, QualifiedParser};
use bitflags::bitflags;

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
}

#[derive(Clone, Debug, PartialEq)]
pub struct Derived {
    pub attributes: Option<Attributes>,
    pub name: Qualified,
    pub specifier: ClassSpecifier,
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

#[derive(Clone, Debug, PartialEq)]
pub struct ClassBody {
    pub public: Members,
    pub protected: Members,
    pub private: Members,
}

struct DerivedParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DerivedParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Derived>) {
        // optional: attributes
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(tok);

        // access-specifier | virtual-specifier
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut specifier = ClassSpecifier::empty();
        while specifier.from_tok(&tok.tok) {
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

        let tok = loop {
            let dp = DerivedParser::new(self.lexer);
            let (tok, derived) = dp.parse(None);

            if let Some(derived) = derived {
                bases.push(derived);
            } else {
                break tok;
            }

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok.tok != Token::Comma {
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

pub(crate) struct ClassParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ClassParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Class>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let kind = if let Some(kind) = Kind::from_tok(&tok.tok) {
            kind
        } else {
            return (Some(tok), None);
        };

        // optional: attributes
        // TODO: alignas
        let ap = AttributesParser::new(self.lexer);
        let (tok, attributes) = ap.parse(None);

        // optional: name
        let qp = QualifiedParser::new(self.lexer);
        let (tok, name) = qp.parse(tok, None);

        // optional: final
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let (tok, r#final) = if tok.tok == Token::Final {
            (None, true)
        } else {
            (Some(tok), false)
        };

        // optional: base-clause
        let bcp = BaseClauseParser::new(self.lexer);
        let (tok, bases) = bcp.parse(tok);

        let cbp = ClassBodyParser::new(self.lexer);
        let (tok, body) = cbp.parse(tok, kind.clone());

        let class = Class {
            kind,
            name,
            attributes,
            r#final,
            bases,
            body,
        };

        (tok, Some(class))
    }
}

pub struct ClassBodyParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ClassBodyParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        kind: Kind,
    ) -> (Option<LocToken>, Option<ClassBody>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftBrace {
            return (Some(tok), None);
        }

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
            let (tk, memb) = mp.parse(tok);

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
                return (tk, Some(body));
            };

            let tk = tk.unwrap_or_else(|| self.lexer.next_useful());
            tok = if tk.tok == Token::RightBrace {
                return (None, Some(body));
            } else {
                Some(tk)
            };
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
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
        let (_, c) = p.parse(None);
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
                    Member::Type(TypeDeclarator {
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
                    }),
                    Member::Type(TypeDeclarator {
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
                    }),
                ],
                protected: vec![Member::Type(TypeDeclarator {
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
                })],
                private: vec![
                    Member::Type(TypeDeclarator {
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
                    }),
                    Member::Type(TypeDeclarator {
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
                    }),
                ],
            }),
        };

        assert_eq!(c, expected);
    }
}
