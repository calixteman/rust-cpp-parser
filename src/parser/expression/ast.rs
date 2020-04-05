use super::operator::*;
use super::params::Parameters;
use crate::parser::name::Qualified;

#[derive(Clone, Debug, PartialEq)]
pub struct UInt {
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Node {
    UnaryOp(Box<UnaryOp>),
    BinaryOp(Box<BinaryOp>),
    CallExpr(Box<CallExpr>),
    Qualified(Box<Qualified>),
    UInt(Box<UInt>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallExpr {
    pub callee: Node,
    pub params: Parameters,
}
