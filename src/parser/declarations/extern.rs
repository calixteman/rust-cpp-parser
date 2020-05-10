// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{
    DeclHint, Declaration, DeclarationListParser, Declarations, Specifier, TypeDeclaratorParser,
};
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;

#[derive(Clone, Debug, PartialEq)]
pub struct Extern {
    pub language: String,
    pub decls: Declarations,
    pub multiple: bool,
}

pub struct ExternParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ExternParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<Token>) -> (Option<Token>, Option<Declaration>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Extern {
            return (Some(tok), None);
        }

        let tok = self.lexer.next_useful();

        if let Token::LiteralString(language) = tok {
            let dlp = DeclarationListParser::new(self.lexer);

            let (tok, list, multiple) = dlp.parse(None);

            (
                tok,
                Some(Declaration::Extern(Extern {
                    language,
                    decls: list.unwrap(),
                    multiple,
                })),
            )
        } else {
            let tdp = TypeDeclaratorParser::new(self.lexer);
            let hint = DeclHint::Specifier(Specifier::EXTERN);
            let (tok, typ) = tdp.parse(Some(tok), Some(hint), true);

            (tok, Some(Declaration::Type(typ.unwrap())))
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::declarations::{types, *};
    use crate::parser::names::*;
    use crate::parser::types::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_extern_c() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
extern "C" {
    double sqrt(double);
}
        "#,
        );
        let p = ExternParser::new(&mut l);
        let (_, ext) = p.parse(None);

        let ext = ext.unwrap();

        assert_eq!(
            ext,
            Declaration::Extern(Extern {
                language: "C".to_string(),
                decls: vec![Declaration::Type(TypeDeclarator {
                    typ: Type {
                        base: BaseType::Function(Box::new(Function {
                            return_type: Some(Type {
                                base: BaseType::Primitive(Primitive::Double),
                                cv: CVQualifier::empty(),
                                pointers: None,
                            }),
                            params: vec![Parameter {
                                attributes: None,
                                decl: TypeDeclarator {
                                    typ: Type {
                                        base: BaseType::Primitive(Primitive::Double),
                                        cv: CVQualifier::empty(),
                                        pointers: None,
                                    },
                                    specifier: Specifier::empty(),
                                    identifier: types::Identifier {
                                        identifier: None,
                                        attributes: None
                                    },
                                    init: None
                                },
                            }],
                            cv: CVQualifier::empty(),
                            refq: RefQualifier::None,
                            except: None,
                            attributes: None,
                            trailing: None,
                            virt_specifier: VirtSpecifier::empty(),
                            status: FunStatus::None,
                            requires: None,
                            ctor_init: None,
                            body: None
                        })),
                        cv: CVQualifier::empty(),
                        pointers: None,
                    },
                    specifier: Specifier::empty(),
                    identifier: types::Identifier {
                        identifier: Some(mk_id!("sqrt")),
                        attributes: None
                    },
                    init: None,
                })],
                multiple: true,
            })
        );
    }

    #[test]
    fn test_extern_decl() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
extern double sqrt(double);
        "#,
        );
        let p = ExternParser::new(&mut l);
        let (_, ext) = p.parse(None);

        let ext = ext.unwrap();

        assert_eq!(
            ext,
            Declaration::Type(TypeDeclarator {
                typ: Type {
                    base: BaseType::Function(Box::new(Function {
                        return_type: Some(Type {
                            base: BaseType::Primitive(Primitive::Double),
                            cv: CVQualifier::empty(),
                            pointers: None,
                        }),
                        params: vec![Parameter {
                            attributes: None,
                            decl: TypeDeclarator {
                                typ: Type {
                                    base: BaseType::Primitive(Primitive::Double),
                                    cv: CVQualifier::empty(),
                                    pointers: None,
                                },
                                specifier: Specifier::empty(),
                                identifier: types::Identifier {
                                    identifier: None,
                                    attributes: None
                                },
                                init: None
                            },
                        }],
                        cv: CVQualifier::empty(),
                        refq: RefQualifier::None,
                        except: None,
                        attributes: None,
                        trailing: None,
                        virt_specifier: VirtSpecifier::empty(),
                        status: FunStatus::None,
                        requires: None,
                        ctor_init: None,
                        body: None
                    })),
                    cv: CVQualifier::empty(),
                    pointers: None,
                },
                specifier: Specifier::EXTERN,
                identifier: types::Identifier {
                    identifier: Some(mk_id!("sqrt")),
                    attributes: None
                },
                init: None,
            })
        );
    }
}
