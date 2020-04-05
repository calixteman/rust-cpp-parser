use super::ast::Node;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operator {
    ScopeResolution,
    PostInc,
    PostDec,
    Call,
    Parenthesis,
    Dot,
    Arrow,
    Subscript,
    PreInc,
    PreDec,
    Plus,
    Minus,
    Indirection,
    AddressOf,
    Sizeof,
    New,
    NewArray,
    Delete,
    DeleteArray,
    CoAwait,
    Not,
    BitNeg,
    DotIndirection,
    ArrowIndirection,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    LShift,
    RShift,
    ThreeWayComp,
    Lt,
    Gt,
    Leq,
    Geq,
    Eq,
    Neq,
    BitAnd,
    BitXor,
    BitOr,
    And,
    Or,
    Question,
    Colon,
    Throw,
    CoYield,
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    LShiftAssign,
    RShiftAssign,
    AndAssign,
    XorAssign,
    OrAssign,
    Comma,
}

impl Operator {
    pub fn operate(&self, stack: &mut Vec<Node>) {
        use Operator::*;

        match *self {
            Plus | Minus | Not | BitNeg | Sizeof | PreInc | PreDec | Indirection | AddressOf => {
                let arg = stack.pop().unwrap();
                stack.push(Node::UnaryOp(Box::new(UnaryOp { op: *self, arg })));
            }
            _ => {
                let arg2 = stack.pop().unwrap();
                let arg1 = stack.pop().unwrap();
                stack.push(Node::BinaryOp(Box::new(BinaryOp {
                    op: *self,
                    arg1,
                    arg2,
                })));
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOp {
    pub op: Operator,
    pub arg1: Node,
    pub arg2: Node,
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOp {
    pub op: Operator,
    pub arg: Node,
}
