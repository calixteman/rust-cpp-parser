// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::errors::{Span, StringlyError};

#[derive(Clone, Debug)]
pub enum LexerError {
    ErrorDirective { sp: Span, msg: String },
    EndifWithoutPreceedingIf { sp: Span },
}

impl LexerError {
    pub fn stringly(&self) -> StringlyError {
        use self::LexerError::*;
        let (sp, message) = match self {
            ErrorDirective { sp, msg } => (*sp, format!("reached #error directive: {}", msg)),
            EndifWithoutPreceedingIf { sp } => {
                (*sp, "reached #endif without preceeding #if".to_owned())
            }
        };
        StringlyError { message, sp }
    }
}
