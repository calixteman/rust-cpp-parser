// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use super::ExprNode;
use crate::parser::dump::Dump;

#[derive(Clone, Copy, Debug, PartialEq, Hash)]
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
    AddressOfLabel,
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
    Conditional,
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
    Cast,
}

impl Operator {
    pub fn operate(self, stack: &mut Vec<ExprNode>) {
        use Operator::*;

        match self {
            Plus | Minus | Not | BitNeg | Sizeof | PreInc | PreDec | Indirection | AddressOf => {
                let arg = stack.pop().unwrap();
                stack.push(ExprNode::UnaryOp(Box::new(UnaryOp { op: self, arg })));
            }
            Conditional => {
                let right = stack.pop().unwrap();
                let left = stack.pop().unwrap();
                let condition = stack.pop().unwrap();
                stack.push(ExprNode::Conditional(Box::new(super::Conditional {
                    condition,
                    left,
                    right,
                })));
            }
            _ => {
                let arg2 = stack.pop().unwrap();
                let arg1 = stack.pop().unwrap();
                stack.push(ExprNode::BinaryOp(Box::new(BinaryOp {
                    op: self,
                    arg1,
                    arg2,
                })));
            }
        }
    }

    pub fn to_str(self) -> &'static str {
        use Operator::*;

        match self {
            ScopeResolution => "::",
            PostInc => "()++",
            PostDec => "()--",
            Call => "()",
            Parenthesis => "(",
            Dot => ".",
            Arrow => "->",
            Subscript => "[]",
            PreInc => "++()",
            PreDec => "--()",
            Plus => "+",
            Minus => "-",
            Indirection => "indirection",
            AddressOf => "address-of",
            AddressOfLabel => "&&",
            Sizeof => "sizeof",
            New => "new",
            NewArray => "new []",
            Delete => "delete",
            DeleteArray => "delete []",
            CoAwait => "co_await",
            Not => "!",
            BitNeg => "~",
            DotIndirection => ".*",
            ArrowIndirection => "->*",
            Mul => "*",
            Div => "/",
            Mod => "%",
            Add => "+",
            Sub => "-",
            LShift => "<<",
            RShift => ">>",
            ThreeWayComp => "<=>",
            Lt => "<",
            Gt => ">",
            Leq => "<=",
            Geq => ">=",
            Eq => "==",
            Neq => "!=",
            BitAnd => "&",
            BitXor => "^",
            BitOr => "|",
            And => "&&",
            Or => "||",
            Conditional => "?:",
            Throw => "throw",
            CoYield => "coyield",
            Assign => "=",
            AddAssign => "+=",
            SubAssign => "-=",
            MulAssign => "*=",
            DivAssign => "/=",
            ModAssign => "%=",
            LShiftAssign => "<<=",
            RShiftAssign => ">>=",
            AndAssign => "&=",
            XorAssign => "^=",
            OrAssign => "|=",
            Comma => ",",
            Cast => "()",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOp {
    pub op: Operator,
    pub arg1: ExprNode,
    pub arg2: ExprNode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOp {
    pub op: Operator,
    pub arg: ExprNode,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Conditional {
    pub condition: ExprNode,
    pub left: ExprNode,
    pub right: ExprNode,
}

impl Dump for BinaryOp {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let prefix = dump_start!(name, self.op.to_str(), prefix, last, stdout);
        dump_fields!(self, prefix, stdout, arg1, arg2);
    }
}

impl Dump for UnaryOp {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let prefix = dump_start!(name, self.op.to_str(), prefix, last, stdout);
        dump_fields!(self, prefix, stdout, arg);
    }
}

impl Dump for Conditional {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let prefix = dump_start!(
            name,
            "conditional(\u{b7}?\u{b7}:\u{b7})",
            prefix,
            last,
            stdout
        );
        dump_fields!(self, prefix, stdout, condition, left, right);
    }
}
