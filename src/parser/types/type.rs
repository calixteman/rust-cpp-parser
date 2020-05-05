// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::cv::CVQualifier;
use super::primitive::Primitive;
use crate::parser::declarations::{Array, Class, Enum, Function, Pointers};
use crate::parser::names::Qualified;

#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    None,
    Auto,
    Primitive(Primitive),
    UD(Qualified),
    Enum(Box<Enum>),
    Class(Box<Class>),
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
