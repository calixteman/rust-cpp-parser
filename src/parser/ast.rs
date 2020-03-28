use super::operator::*;

#[derive(Debug, PartialEq)]
pub struct Id {
    pub name: String,
}

#[derive(Debug, PartialEq)]
pub struct UInt {
    pub value: u32,
}

#[derive(Debug, PartialEq)]
pub enum Node {
    UnaryOp(Box<UnaryOp>),
    BinaryOp(Box<BinaryOp>),
    Arguments(Box<Arguments>),
    CallExpr(Box<CallExpr>),
    Id(Box<Id>),
    UInt(Box<UInt>),
}

#[derive(Debug, PartialEq)]
pub struct Arguments {
    pub args: Vec<Node>,
}

#[derive(Debug, PartialEq)]
pub struct CallExpr {
    pub callee: Node,
    pub args: Node,
}
