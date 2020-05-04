// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::lexer::Location;
use crate::lexer::source::FileId;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilerPhase {
    Lexer,
    Parser,
}

#[derive(Debug, Clone)]
pub struct Error {
    pub phase: CompilerPhase,
    pub message: String,
    pub span: (Option<FileId>, Location, Location),
}

impl Error {
    pub fn new(
        phase: CompilerPhase,
        span: (Option<FileId>, Location, Location),
        message: String,
    ) -> Self {
        Self {
            phase,
            span,
            message,
        }
    }
}
