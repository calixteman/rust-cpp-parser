// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::{TLexer, Token};
use crate::parser::declarations::{
    pointer::{PointerDeclaratorParser, Pointers},
    types::DeclSpecifierParser,
};
use crate::parser::errors::ParserError;
use crate::parser::expressions;
use crate::parser::types::{
    r#type::{BaseType, Type},
    CVQualifier, Primitive, UserDefined,
};
use crate::parser::Context;

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum ConvBaseType {
    Primitive(Primitive),
    UD(Box<UserDefined>),
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub struct ConvType {
    pub base: ConvBaseType,
    pub cv: CVQualifier,
    pub pointers: Option<Pointers>,
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum Operator {
    Op(expressions::Operator),
    UD(String),
    Conv(ConvType),
}

impl Operator {
    pub fn is_conv(&self) -> bool {
        match self {
            Operator::Op(_) | Operator::UD(_) => false,
            _ => true,
        }
    }
}

impl ToString for Operator {
    fn to_string(&self) -> String {
        match self {
            Operator::Op(op) => format!("operator {}", op.to_str()),
            Operator::UD(s) => format!("operator \"\" {}", s),
            Operator::Conv(_) => "conv operator".to_string(),
        }
    }
}

pub(crate) struct OperatorParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> OperatorParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Operator>), ParserError> {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok != Token::Operator {
            return Ok((Some(tok), None));
        }

        let tok = self.lexer.next_useful();
        match tok {
            Token::LiteralString(_) => {
                let tok = self.lexer.next_useful();
                if let Token::Identifier(id) = tok {
                    Ok((None, Some(Operator::UD(id))))
                } else {
                    Err(ParserError::InvalidTokenInOp {
                        sp: self.lexer.span(),
                        tok,
                    })
                }
            }
            Token::LiteralStringUD(s_ud) => {
                let (_, ud) = *s_ud;
                Ok((None, Some(Operator::UD(ud))))
            }
            Token::New => {
                let tok = self.lexer.next_useful();
                if tok == Token::LeftBrack {
                    let tok = self.lexer.next_useful();
                    if tok == Token::RightBrack {
                        Ok((None, Some(Operator::Op(expressions::Operator::NewArray))))
                    } else {
                        Err(ParserError::InvalidTokenInOp {
                            sp: self.lexer.span(),
                            tok,
                        })
                    }
                } else {
                    Ok((Some(tok), Some(Operator::Op(expressions::Operator::New))))
                }
            }
            Token::Delete => {
                let tok = self.lexer.next_useful();
                if tok == Token::LeftBrack {
                    let tok = self.lexer.next_useful();
                    if tok == Token::RightBrack {
                        Ok((None, Some(Operator::Op(expressions::Operator::DeleteArray))))
                    } else {
                        Err(ParserError::InvalidTokenInOp {
                            sp: self.lexer.span(),
                            tok,
                        })
                    }
                } else {
                    Ok((Some(tok), Some(Operator::Op(expressions::Operator::Delete))))
                }
            }
            Token::CoAwait => Ok((None, Some(Operator::Op(expressions::Operator::CoAwait)))),
            Token::LeftParen => {
                let tok = self.lexer.next_useful();
                if tok == Token::RightParen {
                    Ok((None, Some(Operator::Op(expressions::Operator::Call))))
                } else {
                    Err(ParserError::InvalidTokenInOp {
                        sp: self.lexer.span(),
                        tok,
                    })
                }
            }
            Token::LeftBrack => {
                let tok = self.lexer.next_useful();
                if tok == Token::RightBrack {
                    Ok((None, Some(Operator::Op(expressions::Operator::Subscript))))
                } else {
                    Err(ParserError::InvalidTokenInOp {
                        sp: self.lexer.span(),
                        tok,
                    })
                }
            }
            Token::Arrow => Ok((None, Some(Operator::Op(expressions::Operator::Arrow)))),
            Token::ArrowStar => Ok((
                None,
                Some(Operator::Op(expressions::Operator::ArrowIndirection)),
            )),
            Token::Tilde => Ok((None, Some(Operator::Op(expressions::Operator::BitNeg)))),
            Token::Not => Ok((None, Some(Operator::Op(expressions::Operator::Not)))),
            Token::Plus => Ok((None, Some(Operator::Op(expressions::Operator::Plus)))),
            Token::Minus => Ok((None, Some(Operator::Op(expressions::Operator::Minus)))),
            Token::Star => Ok((None, Some(Operator::Op(expressions::Operator::Indirection)))),
            Token::Divide => Ok((None, Some(Operator::Op(expressions::Operator::Div)))),
            Token::Modulo => Ok((None, Some(Operator::Op(expressions::Operator::Mod)))),
            Token::Xor => Ok((None, Some(Operator::Op(expressions::Operator::BitXor)))),
            Token::And => Ok((None, Some(Operator::Op(expressions::Operator::AddressOf)))),
            Token::Or => Ok((None, Some(Operator::Op(expressions::Operator::BitOr)))),
            Token::Equal => Ok((None, Some(Operator::Op(expressions::Operator::Assign)))),
            Token::PlusEqual => Ok((None, Some(Operator::Op(expressions::Operator::AddAssign)))),
            Token::MinusEqual => Ok((None, Some(Operator::Op(expressions::Operator::SubAssign)))),
            Token::StarEqual => Ok((None, Some(Operator::Op(expressions::Operator::MulAssign)))),
            Token::DivideEqual => Ok((None, Some(Operator::Op(expressions::Operator::DivAssign)))),
            Token::ModuloEqual => Ok((None, Some(Operator::Op(expressions::Operator::ModAssign)))),
            Token::XorEqual => Ok((None, Some(Operator::Op(expressions::Operator::XorAssign)))),
            Token::AndEqual => Ok((None, Some(Operator::Op(expressions::Operator::AndAssign)))),
            Token::OrEqual => Ok((None, Some(Operator::Op(expressions::Operator::OrAssign)))),
            Token::EqualEqual => Ok((None, Some(Operator::Op(expressions::Operator::Eq)))),
            Token::NotEqual => Ok((None, Some(Operator::Op(expressions::Operator::Neq)))),
            Token::Lower => Ok((None, Some(Operator::Op(expressions::Operator::Lt)))),
            Token::Greater => Ok((None, Some(Operator::Op(expressions::Operator::Gt)))),
            Token::LowerEqual => Ok((None, Some(Operator::Op(expressions::Operator::Leq)))),
            Token::GreaterEqual => Ok((None, Some(Operator::Op(expressions::Operator::Geq)))),
            Token::LowerEqualGreater => Ok((
                None,
                Some(Operator::Op(expressions::Operator::ThreeWayComp)),
            )),
            Token::AndAnd => Ok((None, Some(Operator::Op(expressions::Operator::And)))),
            Token::OrOr => Ok((None, Some(Operator::Op(expressions::Operator::Or)))),
            Token::LeftShift => Ok((None, Some(Operator::Op(expressions::Operator::LShift)))),
            Token::RightShift => Ok((None, Some(Operator::Op(expressions::Operator::RShift)))),
            Token::LeftShiftEqual => Ok((
                None,
                Some(Operator::Op(expressions::Operator::LShiftAssign)),
            )),
            Token::RightShiftEqual => Ok((
                None,
                Some(Operator::Op(expressions::Operator::RShiftAssign)),
            )),
            Token::PlusPlus => Ok((None, Some(Operator::Op(expressions::Operator::PreInc)))),
            Token::MinusMinus => Ok((None, Some(Operator::Op(expressions::Operator::PreDec)))),
            Token::Comma => Ok((None, Some(Operator::Op(expressions::Operator::Comma)))),
            tk @ _ => {
                let ctp = ConversionTypeParser::new(self.lexer);
                let (tok, typ) = ctp.parse(Some(tk), context)?;

                if let Some(Type { base, cv, pointers }) = typ {
                    let base = match base {
                        BaseType::Primitive(p) => ConvBaseType::Primitive(p),
                        BaseType::UD(ud) => ConvBaseType::UD(ud),
                        _ => {
                            return Err(ParserError::InvalidTypeInOp {
                                sp: self.lexer.span(),
                                name: base.to_string(),
                            });
                        }
                    };
                    let typ = ConvType { base, cv, pointers };
                    Ok((tok, Some(Operator::Conv(typ))))
                } else {
                    Err(ParserError::InvalidTokenInOp {
                        sp: self.lexer.span(),
                        tok: tok.unwrap(),
                    })
                }

                // TODO: add operator literal: http://eel.is/c++draft/over.literal#nt:literal-operator-id
            }
        }
    }
}

pub struct ConversionTypeParser<'a, L: TLexer> {
    lexer: &'a mut L,
}

impl<'a, L: TLexer> ConversionTypeParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<Type>), ParserError> {
        let dsp = DeclSpecifierParser::new(self.lexer);
        let (tok, (_, typ, _, _)) = dsp.parse(tok, None, context)?;

        let mut typ = if let Some(typ) = typ {
            typ
        } else {
            return Ok((tok, None));
        };

        // Pointer: *, &, &&
        let pdp = PointerDeclaratorParser::new(self.lexer);
        let (tok, ptrs) = pdp.parse(tok, None, context)?;
        typ.pointers = ptrs;

        Ok((tok, Some(typ)))
    }
}
