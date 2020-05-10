// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::{Statement, StatementParser};
use crate::lexer::lexer::{Lexer, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::attributes::Attributes;

use crate::dump_start;
use crate::parser::dump::Dump;
use termcolor::StandardStreamLock;

#[derive(Clone, Debug, PartialEq)]
pub struct Compound {
    pub(crate) attributes: Option<Attributes>,
    pub(crate) stmts: Vec<Statement>,
}

impl Dump for Compound {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let prefix = dump_start!(name, "compound", prefix, last, stdout);
        self.attributes
            .dump("attributes", &prefix, self.stmts.is_empty(), stdout);

        let mut count = 1;
        if let Some((last, stmts)) = self.stmts.split_last() {
            for stmt in stmts.iter() {
                stmt.dump(&format!("stmt{}", count), &prefix, false, stdout);
                count += 1;
            }
            last.dump(&format!("stmt{}", count), &prefix, true, stdout);
        }
    }
}

pub struct CompoundStmtParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> CompoundStmtParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, attributes: Option<Attributes>) -> (Option<Token>, Option<Compound>) {
        let mut stmts = Vec::new();
        let mut tok = self.lexer.next_useful();

        loop {
            if tok == Token::RightBrace {
                return (None, Some(Compound { attributes, stmts }));
            }

            let sp = StatementParser::new(self.lexer);
            let (tk, stmt) = sp.parse(Some(tok));

            if let Some(stmt) = stmt {
                stmts.push(stmt);
            }

            tok = tk.unwrap_or_else(|| self.lexer.next_useful());
        }
    }
}
