// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::lexer::Location;
use crate::lexer::source::FileId;
use crate::lexer::errors::LexerError;

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub file: Option<FileId>,
    pub start: Location,
    pub end: Location,
}

#[derive(Debug, Clone)]
pub enum Error {
    LexerError(LexerError),
}

impl Error {
    pub fn stringly(&self) -> StringlyError {
        let stringly = match self {
            Error::LexerError(le) => le.stringly(),
        };
        stringly
    }
}

pub struct StringlyError {
    pub message: String,
    pub sp: Span,
}
