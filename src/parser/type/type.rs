use super::cv::CVQualifier;
use super::primitive::Primitive;

#[derive(Clone, Debug, PartialEq)]
pub enum BaseType {
    Primitive(Primitive),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub(crate) base: BaseType,
    pub(crate) cv: CVQualifier,
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
