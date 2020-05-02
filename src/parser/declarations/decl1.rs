use super::super::r#type::{self, BaseType, CVQualifier, Type};
use super::array::{Array, ArrayParser};
use super::function::{Function, FunctionParser};
use super::pointer::{Pointer, PointerDeclaratorParser, PtrKind};
use super::r#enum::{Enum, EnumParser};
use super::specifier::Specifier;
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::attributes::{Attributes, AttributesParser};
use crate::parser::initializer::{Initializer, InitializerParser};
use crate::parser::names::{Qualified, QualifiedParser};

pub struct DeclarationParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
    ) -> (Option<LocToken>, Option<Declaration>) {
        

    }
}

#[cfg(test)]
mod tests {

    use super::super::function::*;
    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::attributes::Attribute;
    use crate::parser::declarations::pointer::*;
    use crate::parser::expression::*;
    use crate::parser::literals::{self, *};
    use crate::parser::names::Name;
    use crate::parser::r#type::Primitive;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_primitive() {
    }
}
