// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expression::{ExprNode, ExpressionParser};

#[derive(Clone, Debug, PartialEq)]
pub struct StaticAssert {
    pub condition: ExprNode,
    pub string: Option<String>,
    pub cpp: bool,
}

struct StaticAssertParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> StaticAssertParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<StaticAssert>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::StaticAssert && tok.tok != Token::CStaticAssert {
            return (Some(tok), None);
        }

        let cpp = tok.tok == Token::StaticAssert;

        let tok = self.lexer.next_useful();
        if tok.tok != Token::LeftParen {
            unreachable!("Invalid token in static_assert: {:?}", tok);
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
        let (tok, expr) = ep.parse(None);

        let condition = if let Some(cond) = expr {
            cond
        } else {
            unreachable!("Invalid token in static_assert: {:?}", tok)
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok.tok {
            Token::RightParen => {
                return (
                    None,
                    Some(StaticAssert {
                        condition,
                        string: None,
                        cpp,
                    }),
                )
            }
            Token::Comma => {}
            _ => unreachable!("Invalid token in static_assert: {:?}", tok),
        }

        let tok = self.lexer.next_useful();
        let string = tok.tok.get_string();
        if string.is_none() {
            unreachable!("Invalid second argument in static_assert")
        }

        let tok = self.lexer.next_useful();
        if tok.tok != Token::RightParen {
            unreachable!("Invalid token in static_assert: {:?}", tok)
        }

        (
            None,
            Some(StaticAssert {
                condition,
                string,
                cpp,
            }),
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::expression::*;
    use crate::parser::names::Qualified;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_static_assert_1() {
        let mut l = Lexer::<DefaultContext>::new(b"static_assert(a != b)");
        let p = StaticAssertParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            StaticAssert {
                condition: node!(BinaryOp {
                    op: Operator::Neq,
                    arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                    arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                }),
                string: None,
                cpp: true,
            }
        );
    }

    #[test]
    fn test_static_assert_2() {
        let mut l = Lexer::<DefaultContext>::new(b"_Static_assert(a != b, \"an assertion\")");
        let p = StaticAssertParser::new(&mut l);
        let (_, u) = p.parse(None);

        assert_eq!(
            u.unwrap(),
            StaticAssert {
                condition: node!(BinaryOp {
                    op: Operator::Neq,
                    arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                    arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                }),
                string: Some("an assertion".to_string()),
                cpp: false,
            }
        );
    }
}
