// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::hash::{Hash, Hasher};
use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::cv::CVQualifier;
use super::primitive::Primitive;
use crate::parser::context::TypeToFix;
use crate::parser::declarations::types::TypeDeclarator;
use crate::parser::declarations::{Array, Class, Enum, Function, Pointers};
use crate::parser::dump::Dump;
use crate::parser::names::Qualified;

#[derive(Clone, Debug, PartialEq)]
pub enum UDType {
    Direct(Rc<TypeDeclarator>),
    // Used when a type is used insided itself:
    // struct A { ... A* ... }
    // Once the struct is parsed then the Indirect value is set
    Indirect(TypeToFix),
}

impl Dump for UDType {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        match self {
            Self::Direct(_) => dump_str!(name, "<direct>", Cyan, prefix, last, stdout),
            Self::Indirect(i) => i.dump(name, prefix, last, stdout),
        };
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UserDefined {
    pub name: Qualified,
    pub typ: UDType,
}

impl Hash for UserDefined {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Dump for UserDefined {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "UD", prefix, last, stdout, name, typ);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    None,
    Auto,
    Primitive(Primitive),
    UD(Box<UserDefined>),
    Enum(Box<Enum>),
    Class(Box<Class>),
    Function(Box<Function>),
    Array(Box<Array>),
}

impl ToString for BaseType {
    fn to_string(&self) -> String {
        use BaseType::*;

        match self {
            None => "<none>".to_string(),
            Auto => "auto".to_string(),
            Primitive(p) => p.to_str().to_string(),
            UD(ud) => ud.name.to_string(),
            Enum(_) => "enum".to_string(),
            Class(_) => "class".to_string(),
            Function(_) => "function".to_string(),
            Array(_) => "array".to_string(),
        }
    }
}

impl Dump for BaseType {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident ) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::None => dump_str!(name, "None", Cyan, prefix, last, stdout),
            Self::Auto => dump_str!(name, "auto", Cyan, prefix, last, stdout),
            Self::Primitive(x) => dump!(x),
            Self::UD(x) => dump!(x),
            Self::Enum(x) => dump!(x),
            Self::Class(x) => dump!(x),
            Self::Function(x) => dump!(x),
            //Self::Array(x) => dump!(x),
            _ => {}
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub base: BaseType,
    pub cv: CVQualifier,
    pub pointers: Option<Pointers>,
}

impl Dump for Type {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "type", prefix, last, stdout, base, cv, pointers);
    }
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
