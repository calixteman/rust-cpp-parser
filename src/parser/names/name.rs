// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{Parameters, ParametersParser};

use super::dtor::{Destructor, DtorParser};
use super::operator::{Operator, OperatorParser};

#[derive(Clone, Debug, PartialEq)]
pub struct Identifier {
    pub val: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Template {
    id: Identifier,
    params: Parameters,
    //keyword: bool, TODO: set to true when we've A::template B<...>::...
}

#[derive(Clone, Debug, PartialEq)]
pub enum Name {
    Identifier(Identifier),
    Destructor(Destructor),
    Template(Template),
    Operator(Box<Operator>),
    Empty,
    //Decltype(ExprNode), TODO: add that
}

#[macro_export]
macro_rules! mk_id {
    ( $( $name:expr ),* ) => {
        Qualified {
            names: vec![
                $(
                    crate::parser::names::Name::Identifier(crate::parser::names::Identifier { val: $name.to_string()}),
                )*
            ],
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Qualified {
    pub names: Vec<Name>,
}

impl Qualified {
    pub fn is_conv_op(&self) -> bool {
        if let Name::Operator(op) = self.names.last().unwrap() {
            op.is_conv()
        } else {
            false
        }
    }
}

pub struct QualifiedParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> QualifiedParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
        first: Option<String>,
    ) -> (Option<LocToken>, Option<Qualified>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        let mut names = Vec::new();
        let mut wait_id = if let Some(val) = first {
            names.push(Name::Identifier(Identifier { val }));
            false
        } else {
            true
        };

        loop {
            match tok.tok {
                Token::ColonColon => {
                    if names.is_empty() {
                        // ::foo::bar
                        names.push(Name::Empty);
                    }
                    wait_id = true;
                }
                Token::Lower => {
                    let id = if let Some(Name::Identifier(id)) = names.pop() {
                        id
                    } else {
                        unreachable!("Cannot have two templates args");
                    };

                    let pp = ParametersParser::new(self.lexer, Token::Greater);
                    let (_, params) = pp.parse(None, None);

                    names.push(Name::Template(Template {
                        id,
                        params: params.unwrap(),
                    }));

                    wait_id = false;
                }
                Token::Identifier(val) if wait_id => {
                    names.push(Name::Identifier(Identifier { val }));
                    wait_id = false;
                }
                Token::Identifier(_) if !wait_id => {
                    return (Some(tok), Some(Qualified { names }));
                }
                Token::Operator => {
                    let op = OperatorParser::new(self.lexer);
                    let (tok, operator) = op.parse(Some(tok));

                    names.push(Name::Operator(Box::new(operator.unwrap())));

                    return (tok, Some(Qualified { names }));
                }
                Token::Tilde => {
                    if wait_id {
                        let dp = DtorParser::new(self.lexer);
                        let (tok, dtor) = dp.parse(Some(tok));

                        names.push(Name::Destructor(dtor.unwrap()));
                        return (tok, Some(Qualified { names }));
                    } else {
                        return (Some(tok), Some(Qualified { names }));
                    }
                }
                _ => {
                    if names.is_empty() {
                        return (Some(tok), None);
                    } else {
                        return (Some(tok), Some(Qualified { names }));
                    }
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::expression::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_name_one() {
        let mut l = Lexer::<DefaultContext>::new(b"abc");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(q.unwrap(), mk_id!("abc"));
    }

    #[test]
    fn test_name_two() {
        let mut l = Lexer::<DefaultContext>::new(b"abc::defg");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(q.unwrap(), mk_id!("abc", "defg"));
    }

    #[test]
    fn test_name_three() {
        let mut l = Lexer::<DefaultContext>::new(b"abc::defg::hijkl");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(q.unwrap(), mk_id!("abc", "defg", "hijkl"));
    }

    #[test]
    fn test_name_template_zero() {
        let mut l = Lexer::<DefaultContext>::new(b"A<>");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(
            q.unwrap(),
            Qualified {
                names: vec![Name::Template(Template {
                    id: Identifier {
                        val: "A".to_string()
                    },
                    params: vec![],
                }),],
            }
        );
    }

    #[test]
    fn test_name_template_one() {
        let mut l = Lexer::<DefaultContext>::new(b"A<B>");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(
            q.unwrap(),
            Qualified {
                names: vec![Name::Template(Template {
                    id: Identifier {
                        val: "A".to_string()
                    },
                    params: vec![Some(ExprNode::Qualified(Box::new(mk_id!("B")))),],
                }),],
            }
        );
    }

    #[test]
    fn test_name_complex() {
        let mut l = Lexer::<DefaultContext>::new(b"A::B<C::D, E::F, G>::H<I>");
        let p = QualifiedParser::new(&mut l);
        let (_, q) = p.parse(None, None);

        assert_eq!(
            q.unwrap(),
            Qualified {
                names: vec![
                    Name::Identifier(Identifier {
                        val: "A".to_string(),
                    }),
                    Name::Template(Template {
                        id: Identifier {
                            val: "B".to_string()
                        },
                        params: vec![
                            Some(ExprNode::Qualified(Box::new(mk_id!("C", "D")))),
                            Some(ExprNode::Qualified(Box::new(mk_id!("E", "F")))),
                            Some(ExprNode::Qualified(Box::new(mk_id!("G")))),
                        ]
                    }),
                    Name::Template(Template {
                        id: Identifier {
                            val: "H".to_string()
                        },
                        params: vec![Some(ExprNode::Qualified(Box::new(mk_id!("I")))),]
                    })
                ]
            }
        );
    }
}
