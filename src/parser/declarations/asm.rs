// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use crate::lexer::{TLexer, Token};
use crate::parser::attributes::Attributes;
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::literals::StringLiteralParser;
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq)]
pub struct Asm {
    pub attributes: Option<Attributes>,
    pub code: String,
}

impl Dump for Asm {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "asm", prefix, last, stdout, attributes);
    }
}

pub(crate) struct AsmParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> AsmParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Asm>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Asm {
            return Ok((Some(tok), None));
        }

        let tok = self.lexer.next_useful();
        if tok != Token::LeftParen {
            return Err(ParserError::InvalidTokenInAsm {
                sp: self.lexer.span(),
                tok,
            });
        }

        let tok = self.lexer.next_useful();

        if let Some(code) = tok.get_string() {
            // TODO: add an asm lexer & parser
            let slp = StringLiteralParser::new(self.lexer);
            let (tok, code) = slp.parse(&code, context)?;

            let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
            if tok != Token::RightParen {
                return Err(ParserError::InvalidTokenInAsm {
                    sp: self.lexer.span(),
                    tok,
                });
            }

            Ok((
                None,
                Some(Asm {
                    attributes: None,
                    code,
                }),
            ))
        } else {
            Err(ParserError::InvalidTokenInAsm {
                sp: self.lexer.span(),
                tok: Token::None,
            })
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use pretty_assertions::assert_eq;

    #[test]
    fn test_asm() {
        let mut l = Lexer::<DefaultContext>::new(
            r#"
asm(R"(
.globl func
    .type func, @function
    func:
    .cfi_startproc
    movl $7, %eax
    ret
    .cfi_endproc
)")
"#
            .as_bytes(),
        );
        let p = AsmParser::new(&mut l);
        let mut context = Context::default();
        let (_, u) = p.parse(None, &mut context).unwrap();

        let code = r#"
.globl func
    .type func, @function
    func:
    .cfi_startproc
    movl $7, %eax
    ret
    .cfi_endproc
"#;

        assert_eq!(
            u.unwrap(),
            Asm {
                attributes: None,
                code: code.to_string(),
            }
        );
    }
}
