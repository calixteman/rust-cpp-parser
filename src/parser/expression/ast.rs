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
    SubscriptExpr(Box<SubscriptExpr>),
    Arguments(Box<Arguments>),
    Qualified(Box<Qualified>),
    UInt(Box<UInt>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Arguments {
    pub args: Vec<Node>, // TODO: on utilise ca pr l'op parenthese
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallExpr {
    pub callee: Node,
    pub params: Parameters,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SubscriptExpr {
    pub array: Node,
    pub index: Node,
}
