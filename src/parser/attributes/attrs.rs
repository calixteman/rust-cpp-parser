use crate::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::name::{Qualified, QualifiedParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Simple {
    pub name: Qualified,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Args {
    pub name: Qualified,
    pub args: Vec<>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Attribute {
    pub Simple(Simple),
    pub Args(Args),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Args {
    pub name: String,
}

pub struct AttributedParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    attrs: Vec<Attribute>,
}

impl<'a, 'b, PC: PreprocContext> QualifiedParser <'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            attrs: Vec::new(),
        }
    }

    pub(super) fn parse(mut self) -> (LocToken<'a>, Qualified) {
        // [[ attribute-list ]]
        // [[ using attribute-namespace : attribute-list ]]
        //
        // attributes
        //   identifier 		
        //   attribute-namespace :: identifier 		
        //   identifier ( argument-list ) 		
        //   attribute-namespace :: identifier ( argument-list ) 		
        loop {
            let tok = self.lexer.next_useful();
            match tok.tok {
                Token::Identifier(id) => {
                    let mut qp = QualifiedParser::new_with_name(id);
                    let (tok, qual) = qp.parse();
                    if tok.tok == Token::LeftParen {
                        self.attrs.push(
                            Attribute::Args(Args [

                            })
                        );
                    }
                }
                _ => {
                    return (tok, self.qual);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;

    #[test]
    fn test_name_one() {
        let mut l = Lexer::<DefaultContext>::new(b"abc");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Identifier(Identifier {
                    val: "abc".to_string(),
                })
            ],
        });
    }

    #[test]
    fn test_name_two() {
        let mut l = Lexer::<DefaultContext>::new(b"abc::defg");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Identifier(Identifier {
                    val: "abc".to_string(),
                }),
                Name::Identifier(Identifier {
                    val: "defg".to_string(),
                })
            ],
        });
    }

    #[test]
    fn test_name_three() {
        let mut l = Lexer::<DefaultContext>::new(b"abc::defg::hijkl");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Identifier(Identifier {
                    val: "abc".to_string(),
                }),
                Name::Identifier(Identifier {
                    val: "defg".to_string(),
                }),
                Name::Identifier(Identifier {
                    val: "hijkl".to_string(),
                })
            ],
        });
    }

    #[test]
    fn test_name_template_zero() {
        let mut l = Lexer::<DefaultContext>::new(b"A<>");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Template(Template {
                    val: "A".to_string(),
                    args: vec![
                        Qualified {
                            names: vec![],
                        },
                    ],
                }),
            ],
        });
    }
    
    #[test]
    fn test_name_template_one() {
        let mut l = Lexer::<DefaultContext>::new(b"A<B>");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Template(Template {
                    val: "A".to_string(),
                    args: vec![
                        Qualified {
                            names: vec![
                                Name::Identifier(Identifier {
                                    val: "B".to_string(),
                                })
                            ],
                        },
                    ],
                }),
            ],
        });
    }

    #[test]
    fn test_name_complex() {
        let mut l = Lexer::<DefaultContext>::new(b"A::B<C::D, E::F, G>::H<I>");
        let mut p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse();

        assert_eq!(q, Qualified {
            names: vec![
                Name::Identifier(Identifier {
                    val: "A".to_string(),
                }),
                Name::Template(Template {
                    val: "B".to_string(),
                    args: vec![
                        Qualified {
                            names: vec![
                                Name::Identifier(Identifier {
                                    val: "C".to_string(),
                                }),
                                Name::Identifier(Identifier {
                                    val: "D".to_string(),
                                })
                            ]
                        },
                        Qualified {
                            names: vec![
                                Name::Identifier(Identifier {
                                    val: "E".to_string(),
                                }),
                                Name::Identifier(Identifier {
                                    val: "F".to_string(),
                                })
                            ]
                        },
                        Qualified {
                            names: vec![
                                Name::Identifier(Identifier {
                                    val: "G".to_string(),
                                })
                            ]
                        }
                    ]
                }),
                Name::Template(Template {
                    val: "H".to_string(),
                    args: vec![
                        Qualified {
                            names: vec![
                                Name::Identifier(Identifier {
                                    val: "I".to_string(),
                                })
                            ]
                        }
                    ]
                })
            ]
        });
    }
}
