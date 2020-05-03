// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::expressions::{ExpressionParser, ExprNode, Parameters, ParametersParser};


pub struct TypeOrExprParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> TypeOrExprParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
        }
    }

    fn is_type_token(tok: &Token) -> bool {
        match tok {
            Token::Const
            | Token::Volatile
            | Token::Signed
            | Token::Unsigned
            | Token::Void
            | Token::Char
            | Token::Short
            | Token::Int
            | Token::Long
            | Token::Float
            | Token::Double
            | Token::Bool
            | Token::WcharT
            | Token::Char8T
            | Token::Char16T
            | Token::Char32T
            | Token::Complex
            | Token::Imaginary
            | Token::Struct
            | Token::Class
            | Token::Enum => true,
            _ => false,
        }
    }
    
    pub(super) fn parse(
        self,
        tok: Option<LocToken>,
    ) -> (Option<LocToken>, Option<Qualified>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        if Self::is_type_token(&tok) {
            let dp = DeclarationParser::new(self.lexer);
            let (tok, decl) = dp.parse(tok);

            if let Some(decl) = decl {
                
            } else {
                unreachable!("Invalid type");
            }
        } else if let Token::Identifier(_) = tok  {
            let mut qp = QualifiedParser::new(self.lexer);
            let (tok, qual) = qp.parse(Some(tok));
            if let Some(qual) = qual {
                
            }
        }
    }
}
