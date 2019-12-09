use super::ast::{Arguments, BinaryOp, CallExpr, Id, Node, Operator, UInt, UnaryOp};
use crate::lexer::lexer::{Lexer, Token};

#[derive(Clone, Copy, Debug, PartialEq)]
enum CommaKind {
    Parenthesis,
    Call,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum LastKind {
    Operator,
    Operand,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Associativity {
    LR,
    RL,
}

#[inline(always)]
fn precedence(op: Operator) -> (u32, Associativity) {
    use Operator::*;

    match op {
        Call | Array | Dot | Arrow => (1, Associativity::LR),
        Plus | Minus | Sizeof => (2, Associativity::RL),
        Mul | Div | Mod => (3, Associativity::LR),
        Add | Sub => (4, Associativity::LR),
        LShift | RShift => (5, Associativity::LR),
        Lt | Gt | Leq | Geq => (6, Associativity::LR),
        Eq | Neq => (7, Associativity::LR),
        BitAnd => (8, Associativity::LR),
        BitXor => (9, Associativity::LR),
        BitOr => (10, Associativity::LR),
        And => (11, Associativity::LR),
        Or => (12, Associativity::LR),
        Question | Colon => (13, Associativity::RL),
        Comma | CommaArg => (15, Associativity::LR),
        _ => (0, Associativity::LR),
    }
}

#[inline(always)]
fn is_delimiter(op: Operator) -> bool {
    use Operator::*;

    match op {
        Call | Parenthesis | Array => true,
        _ => false,
    }
}

#[inline(always)]
fn check_precedence(left: Operator, right: Operator) -> bool {
    // TODO: replace this by a table
    // a + b * c => prec(+) <= prec(*) is true so * has precedence on +
    let (l_prec, l_assoc) = precedence(left);
    let (r_prec, r_assoc) = precedence(right);

    (l_prec == r_prec && l_assoc == Associativity::LR) || (l_prec < r_prec)
}

pub struct Expression<'a, 'b> {
    lexer: &'b mut Lexer<'a>,
    operands: Vec<Node>,
    operators: Vec<Operator>,
    comma: Vec<CommaKind>,
    last: LastKind,
}

impl<'a, 'b> Expression<'a, 'b> {
    fn new(lexer: &'b mut Lexer<'a>) -> Self {
        Self {
            lexer,
            operands: Vec::new(),
            operators: Vec::new(),
            comma: Vec::new(),
            last: LastKind::Operator,
        }
    }

    fn push_operator(&mut self, op: Operator) {
        loop {
            if let Some(top) = self.operators.last() {
                if is_delimiter(*top) {
                    break;
                }
                if check_precedence(*top, op) {
                    let top = self.operators.pop().unwrap();
                    top.operate(&mut self.operands);
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.last = LastKind::Operator;
        self.operators.push(op);
    }

    fn flush(&mut self) {
        while let Some(op) = self.operators.pop() {
            //eprintln!("FLUSH {:?}\n{:?}\n", self.operands, self.operators);
            op.operate(&mut self.operands);
        }
    }

    fn flush_until_paren(&mut self) {
        while let Some(op) = self.operators.pop() {
            match op {
                Operator::Parenthesis => {
                    break;
                }
                Operator::Call => {
                    break;
                }
                _ => {
                    op.operate(&mut self.operands);
                }
            }
        }
    }

    fn parse(&mut self) -> Node {
        loop {
            let tok = self.lexer.next_useful();
            match tok {
                Token::Plus => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Add);
                    } else {
                        self.push_operator(Operator::Plus);
                    }
                }
                Token::Minus => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Sub);
                    } else {
                        self.push_operator(Operator::Minus);
                    }
                }
                Token::Sizeof => {
                    // TODO: sizeof takes a type as parameter... not an expression
                    self.push_operator(Operator::Sizeof);
                }
                Token::Not => {
                    self.push_operator(Operator::Not);
                }
                Token::Tilde => {
                    self.push_operator(Operator::BitNeg);
                }
                Token::Star => {
                    self.push_operator(Operator::Mul);
                }
                Token::Divide => {
                    self.push_operator(Operator::Div);
                }
                Token::Modulo => {
                    self.push_operator(Operator::Mod);
                }
                Token::LeftShift => {
                    self.push_operator(Operator::LShift);
                }
                Token::RightShift => {
                    self.push_operator(Operator::RShift);
                }
                Token::Lower => {
                    self.push_operator(Operator::Lt);
                }
                Token::Greater => {
                    self.push_operator(Operator::Gt);
                }
                Token::LowerEqual => {
                    self.push_operator(Operator::Leq);
                }
                Token::GreaterEqual => {
                    self.push_operator(Operator::Geq);
                }
                Token::NotEqual => {
                    self.push_operator(Operator::Neq);
                }
                Token::And => {
                    self.push_operator(Operator::BitAnd);
                }
                Token::Xor => {
                    self.push_operator(Operator::BitXor);
                }
                Token::Or => {
                    self.push_operator(Operator::BitOr);
                }
                Token::AndAnd => {
                    self.push_operator(Operator::And);
                }
                Token::OrOr => {
                    self.push_operator(Operator::Or);
                }
                Token::Question => {
                    self.push_operator(Operator::Question);
                }
                Token::Colon => {
                    self.push_operator(Operator::Colon);
                }
                Token::LeftParen => {
                    self.operators.push(Operator::Parenthesis);
                    if self.last == LastKind::Operand {
                        self.comma.push(CommaKind::Call);
                    } else {
                        self.comma.push(CommaKind::Parenthesis);
                    }
                    self.last = LastKind::Operator;
                }
                Token::Comma => match self.comma.last().unwrap() {
                    CommaKind::Parenthesis => {
                        self.push_operator(Operator::Comma);
                    }
                    CommaKind::Call => {
                        self.push_operator(Operator::CommaArg);
                    }
                },
                Token::RightParen => {
                    self.flush_until_paren();
                    match self.comma.pop().unwrap() {
                        CommaKind::Call => {
                            Operator::Call.operate(&mut self.operands);
                        }
                        _ => {}
                    }
                }
                Token::Identifier(name) => {
                    self.operands.push(Node::Id(Box::new(Id {
                        name: name.to_string(),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralInt(x) => {
                    self.operands
                        .push(Node::UInt(Box::new(UInt { value: x as u32 })));
                    self.last = LastKind::Operand;
                }
                _ => {
                    //eprintln!("COUCOU {:?}\n{:?}\n", self.operands, self.operators);
                    self.flush();
                    return self.operands.pop().unwrap();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::fs;

    #[test]
    fn test_add() {
        let mut lexer = Lexer::new(b"a + b + c");
        let mut parser = Expression::new(&mut lexer);
        let node = parser.parse();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(BinaryOp {
                op: Operator::Add,
                arg1: node!(Id {
                    name: "a".to_string()
                }),
                arg2: node!(Id {
                    name: "b".to_string()
                }),
            }),
            arg2: node!(Id {
                name: "c".to_string()
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_add_associativity() {
        let mut lexer = Lexer::new(b"a + (b + c)");
        let mut parser = Expression::new(&mut lexer);
        let node = parser.parse();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(Id {
                name: "a".to_string()
            }),
            arg2: node!(BinaryOp {
                op: Operator::Add,
                arg1: node!(Id {
                    name: "b".to_string()
                }),
                arg2: node!(Id {
                    name: "c".to_string()
                }),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_priority() {
        let mut lexer = Lexer::new(b"a + b * c");
        let mut parser = Expression::new(&mut lexer);
        let node = parser.parse();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(Id {
                name: "a".to_string()
            }),
            arg2: node!(BinaryOp {
                op: Operator::Mul,
                arg1: node!(Id {
                    name: "b".to_string()
                }),
                arg2: node!(Id {
                    name: "c".to_string()
                }),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_call() {
        let mut lexer = Lexer::new(b"foo(a, b)");
        let mut parser = Expression::new(&mut lexer);
        let node = parser.parse();

        let expected = node!(CallExpr {
            callee: node!(Id {
                name: "foo".to_string()
            }),
            args: node!(Arguments {
                args: vec![
                    node!(Id {
                        name: "a".to_string()
                    }),
                    node!(Id {
                        name: "b".to_string()
                    }),
                ],
            }),
        });

        assert_eq!(node, expected);
    }
}
