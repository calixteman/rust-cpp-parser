// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use crate::lexer::{TLexer, Token};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::expressions::{ExprNode, ExpressionParser};
use crate::parser::literals::StringLiteralParser;
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct StaticAssert {
    pub condition: ExprNode,
    pub string: Option<String>,
    pub cpp: bool,
}

impl Dump for StaticAssert {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(
            self,
            name,
            "static_assert",
            prefix,
            last,
            stdout,
            condition,
            string,
            cpp
        );
    }
}

pub(crate) struct StaticAssertParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> StaticAssertParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<StaticAssert>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::StaticAssert && tok != Token::CStaticAssert {
            return Ok((Some(tok), None));
        }

        let cpp = tok == Token::StaticAssert;

        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            return Err(ParserError::InvalidTokenInStaticAssert {
                sp: self.lexer.span(),
                tok,
            });
        }

        let mut ep = ExpressionParser::new(self.lexer, Token::Comma);
        let (tok, expr) = ep.parse(None, context)?;

        let condition = if let Some(cond) = expr {
            cond
        } else {
            return Err(ParserError::InvalidTokenInStaticAssert {
                sp: self.lexer.span(),
                tok: tok.unwrap(),
            });
        };

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        match tok {
            Token::RightParen => {
                return Ok((
                    None,
                    Some(StaticAssert {
                        condition,
                        string: None,
                        cpp,
                    }),
                ))
            }
            Token::Comma => {}
            _ => {
                return Err(ParserError::InvalidTokenInStaticAssert {
                    sp: self.lexer.span(),
                    tok,
                });
            }
        }

        let tok = self.lexer.next_useful();
        let string = tok.get_string();

        let string = if let Some(string) = string {
            string
        } else {
            return Err(ParserError::InvalidArgInStaticAssert {
                sp: self.lexer.span(),
            });
        };

        let slp = StringLiteralParser::new(self.lexer);
        let (tok, string) = slp.parse(&string, context)?;

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::RightParen {
            return Err(ParserError::InvalidTokenInStaticAssert {
                sp: self.lexer.span(),
                tok,
            });
        }

        Ok((
            None,
            Some(StaticAssert {
                condition,
                string: Some(string),
                cpp,
            }),
        ))
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::mk_var;
    use crate::parser::expressions::*;
    use crate::parser::names::Qualified;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_static_assert_1() {
        let mut l = Lexer::<DefaultContext>::new(b"static_assert(a != b)");
        let p = StaticAssertParser::new(&mut l);
        let mut context = Context::default();
        let (_, u) = p.parse(None, &mut context).unwrap();

        assert_eq!(
            u.unwrap(),
            StaticAssert {
                condition: node!(BinaryOp {
                    op: Operator::Neq,
                    arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
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
        let mut context = Context::default();
        let (_, u) = p.parse(None, &mut context).unwrap();

        assert_eq!(
            u.unwrap(),
            StaticAssert {
                condition: node!(BinaryOp {
                    op: Operator::Neq,
                    arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                }),
                string: Some("an assertion".to_string()),
                cpp: false,
            }
        );
    }
}
