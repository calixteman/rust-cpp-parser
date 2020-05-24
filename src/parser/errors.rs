// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::errors::{Span, StringlyError};
use crate::lexer::Token;

#[derive(Clone, Debug)]
pub enum ParserError {
    InvalidVarInDecl { sp: Span, name: String },
    InvalidTokenInOp { sp: Span, tok: Token },
    InvalidTokenInDtor { sp: Span, tok: Token },
    InvalidTokenInArraySize { sp: Span, tok: Token },
    InvalidTokenInAttrs { sp: Span, tok: Token },
    InvalidTokenInAsm { sp: Span, tok: Token },
    InvalidTokenInExtern { sp: Span, tok: Token },
    InvalidTokenInParamList { sp: Span, tok: Token },
    InvalidTokenInFuncDecl { sp: Span, tok: Token },
    InvalidTokenInThrow { sp: Span, tok: Token },
    InvalidTokenInClass { sp: Span, tok: Token },
    InvalidTokenInNs { sp: Span, tok: Token },
    InvalidTokenInGoto { sp: Span, tok: Token },
    InvalidTokenInIf { sp: Span, tok: Token },
    InvalidTokenInSwitch { sp: Span, tok: Token },
    InvalidTokenInTry { sp: Span, tok: Token },
    InvalidTokenInPointer { sp: Span, tok: Token },
    InvalidTokenInStaticAssert { sp: Span, tok: Token },
    InvalidTokenInUsingEnum { sp: Span, tok: Token },
    InvalidTokenInEnum { sp: Span, tok: Token },
    InvalidTokenInUsing { sp: Span, tok: Token },
    InvalidTokenInAlias { sp: Span, tok: Token },
    InvalidTokenInConditional { sp: Span, tok: Token },
    InvalidTokenInDo { sp: Span, tok: Token },
    InvalidTokenInStmt { sp: Span, tok: Token },
    InvalidTokenInFor { sp: Span, tok: Token },
    InvalidTokenInWhile { sp: Span, tok: Token },
    InvalidTokenInUnit { sp: Span, tok: Token },
    InvalidExprInFor { sp: Span },
    InvalidTypeInOp { sp: Span, name: String },
    InvalidTypeInExpr { sp: Span, name: String },
    UnknownId { sp: Span, name: String },
    InvalidArgInStaticAssert { sp: Span },
    UnbalancedAttr { sp: Span, tok: Token },
    UnexpectedEof { sp: Span },
    InvalidBitfieldSize { sp: Span },
    InvalidCtorInit { sp: Span },
    InvalidCast { sp: Span },
}

impl ParserError {
    pub fn stringly(&self) -> StringlyError {
        use self::ParserError::*;
        let (sp, message) = match self {
            InvalidVarInDecl { sp, name } => {
                (*sp, format!("Invalid variable {} in declaration", name))
            }
            InvalidTokenInOp { sp, tok } => {
                (*sp, format!("Invalid token {:?} in operator name", tok))
            }
            InvalidTokenInDtor { sp, tok } => {
                (*sp, format!("Invalid token {:?} in dtor name", tok))
            }
            InvalidTokenInArraySize { sp, tok } => {
                (*sp, format!("Invalid token {:?} in array size", tok))
            }
            InvalidTokenInAttrs { sp, tok } => {
                (*sp, format!("Invalid token {:?} in attributes", tok))
            }
            InvalidTokenInAsm { sp, tok } => {
                (*sp, format!("Invalid token {:?} in asm declaration", tok))
            }
            InvalidTokenInParamList { sp, tok } => {
                (*sp, format!("Invalid token {:?} in parameter list", tok))
            }
            InvalidTokenInExtern { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in extern declaration", tok),
            ),
            InvalidTokenInFuncDecl { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in function declaration", tok),
            ),
            InvalidTokenInThrow { sp, tok } => (*sp, format!("Invalid token {:?} in throw", tok)),
            InvalidTokenInClass { sp, tok } => {
                (*sp, format!("Invalid token {:?} in class declaration", tok))
            }
            InvalidTokenInNs { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in namespace declaration", tok),
            ),
            InvalidTokenInGoto { sp, tok } => {
                (*sp, format!("Invalid token {:?} in goto statement", tok))
            }
            InvalidTokenInIf { sp, tok } => {
                (*sp, format!("Invalid token {:?} in if statement", tok))
            }
            InvalidTokenInSwitch { sp, tok } => {
                (*sp, format!("Invalid token {:?} in switch statement", tok))
            }
            InvalidTokenInTry { sp, tok } => {
                (*sp, format!("Invalid token {:?} in try statement", tok))
            }
            InvalidTokenInPointer { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in pointer declarator", tok),
            ),
            InvalidTokenInStaticAssert { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in static_assert declarator", tok),
            ),
            InvalidTokenInUsingEnum { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in using enum declaration", tok),
            ),
            InvalidTokenInEnum { sp, tok } => {
                (*sp, format!("Invalid token {:?} in enum declaration", tok))
            }
            InvalidTokenInUsing { sp, tok } => {
                (*sp, format!("Invalid token {:?} in using declaration", tok))
            }
            InvalidTokenInAlias { sp, tok } => {
                (*sp, format!("Invalid token {:?} in alias declaration", tok))
            }
            InvalidTokenInConditional { sp, tok } => (
                *sp,
                format!("Invalid token {:?} in conditional expression", tok),
            ),
            InvalidTokenInDo { sp, tok } => {
                (*sp, format!("Invalid token {:?} in do statement", tok))
            }
            InvalidTokenInStmt { sp, tok } => {
                (*sp, format!("Invalid token {:?} in statement", tok))
            }
            InvalidTokenInFor { sp, tok } => {
                (*sp, format!("Invalid token {:?} in for statement", tok))
            }
            InvalidTokenInWhile { sp, tok } => {
                (*sp, format!("Invalid token {:?} in while statement", tok))
            }
            InvalidTokenInUnit { sp, tok } => (*sp, format!("Invalid token {:?} in CU", tok)),
            InvalidExprInFor { sp } => (*sp, format!("Invalid expression in for statement")),
            InvalidTypeInOp { sp, name } => {
                (*sp, format!("Invalid type {} in conversion operator", name))
            }
            InvalidTypeInExpr { sp, name } => (*sp, format!("Invalid type {} in expression", name)),
            UnknownId { sp, name } => (*sp, format!("Unknown identifier {}", name)),
            UnbalancedAttr { sp, tok } => (*sp, format!("Unbalanced {:?} in attriute", tok)),
            UnexpectedEof { sp } => (*sp, format!("Unexpected eof")),
            InvalidBitfieldSize { sp } => (*sp, format!("Invalid bitfield size")),
            InvalidCtorInit { sp } => (*sp, format!("Invalid ctor initializer")),
            InvalidArgInStaticAssert { sp } => (*sp, format!("Invalid argument in static_assert")),
            InvalidCast { sp } => (*sp, format!("Invalid cast")),
        };
        StringlyError { message, sp }
    }
}

// use crate::parser::errors::ParserError;
// return Err(ParserError:: { sp: self.lexer.span(), tok });
