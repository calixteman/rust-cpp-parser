#[derive(Debug, PartialEq)]
pub struct Id {
    pub name: String,
}

#[derive(Debug, PartialEq)]
pub struct UInt {
    pub value: u32,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operator {
    Call,
    Parenthesis,
    Array,
    Dot,
    Arrow,
    Plus,
    Minus,
    Sizeof,
    Not,
    BitNeg,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    LShift,
    RShift,
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
    Comma,
    CommaArg,
}

impl Operator {
    pub fn operate(&self, stack: &mut Vec<Node>) {
        use Operator::*;

        match *self {
            Plus | Minus | Not | BitNeg | Sizeof => {
                let arg = stack.pop().unwrap();
                stack.push(Node::UnaryOp(Box::new(UnaryOp { op: *self, arg })));
            }
            CommaArg => {
                let arg2 = stack.pop().unwrap();
                if let Node::Arguments(args) = stack.last_mut().unwrap() {
                    args.args.push(arg2);
                } else {
                    let arg1 = stack.pop().unwrap();
                    stack.push(Node::Arguments(Box::new(Arguments {
                        args: vec![arg1, arg2],
                    })));
                }
            }
            Call => {
                let arg2 = stack.pop().unwrap();
                let arg1 = stack.pop().unwrap();
                stack.push(Node::CallExpr(Box::new(CallExpr {
                    callee: arg1,
                    args: arg2,
                })));
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
pub struct BinaryOp {
    pub op: Operator,
    pub arg1: Node,
    pub arg2: Node,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOp {
    pub op: Operator,
    pub arg: Node,
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
