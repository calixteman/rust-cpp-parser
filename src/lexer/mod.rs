// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[macro_export]
macro_rules! error {
    ($span:expr, $($arg:tt)*) => {
        return Err($crate::errors::Error::new(
            $crate::errors::CompilerPhase::Lexer,
            $span,
            format!($($arg)*),
        ));
    };
}

pub mod lexer;
pub use self::lexer::*;

pub mod preprocessor;
pub mod source;

mod buffer;
mod cchar;
mod comment;
mod number;
mod string;
mod tools;
