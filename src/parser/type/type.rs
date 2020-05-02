use super::cv::CVQualifier;
use super::primitive::Primitive;
use crate::parser::declarations::{Array, Enum, Function, Pointers};
use crate::parser::names::Qualified;

#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    None,
    Auto,
    Primitive(Primitive),
    UD(Qualified),
    Enum(Box<Enum>),
    Function(Box<Function>),
    Array(Box<Array>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub base: BaseType,
    pub cv: CVQualifier,
    pub pointers: Option<Pointers>,
}

impl Default for Type {
    fn default() -> Self {
        Self {
            base: BaseType::None,
            cv: CVQualifier::empty(),
            pointers: None,
        }
    }
}

impl Type {
    pub fn base(&self) -> &BaseType {
        &self.base
    }

    pub fn is_const(&self) -> bool {
        self.cv.intersects(CVQualifier::CONST)
    }

    pub fn is_volatile(&self) -> bool {
        self.cv.intersects(CVQualifier::VOLATILE)
    }
}
