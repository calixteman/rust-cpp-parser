use super::context::PreprocContext;
use crate::lexer::lexer::{Lexer, Token};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operator {
    Parenthesis,
    Plus,
    Minus,
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
}

impl Operator {
    #[inline(always)]
    pub(crate) fn operate(self, stack: &mut Vec<Int>) {
        use Operator::*;

        match self {
            Plus => {}
            Minus => {
                stack.last_mut().unwrap().minus();
            }
            Not => {
                stack.last_mut().unwrap().not();
            }
            BitNeg => {
                stack.last_mut().unwrap().bitneg();
            }
            Mul => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().mul(b);
            }
            Div => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().div(b);
            }
            Mod => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().modulo(b);
            }
            Add => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().add(b);
            }
            Sub => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().sub(b);
            }
            LShift => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().lshift(b);
            }
            RShift => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().rshift(b);
            }
            Lt => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().lt(b);
            }
            Gt => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().gt(b);
            }
            Leq => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().leq(b);
            }
            Geq => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().geq(b);
            }
            Eq => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().eq(b);
            }
            Neq => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().neq(b);
            }
            BitAnd => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().bitand(b);
            }
            BitXor => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().bitxor(b);
            }
            BitOr => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().bitor(b);
            }
            And => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().and(b);
            }
            Or => {
                let b = stack.pop().unwrap();
                stack.last_mut().unwrap().or(b);
            }
            Colon => {
                // a ? b : c
                let c = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();

                let cond = match a {
                    Int::Unsigned(x) => x != 0,
                    Int::Signed(x) => x != 0,
                };
                if cond {
                    stack.push(b);
                } else {
                    stack.push(c);
                }
            }
            Question => {}
            _ => {}
        }
    }
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Int {
    Unsigned(u64),
    Signed(i64),
}

impl Int {
    #[inline(always)]
    fn minus(&mut self) {
        *self = match self {
            Int::Unsigned(n) => Int::Signed(-(*n as i64)),
            Int::Signed(n) => Int::Signed(-*n),
        }
    }

    #[inline(always)]
    fn not(&mut self) {
        *self = match self {
            Int::Unsigned(n) => Int::Unsigned((*n == 0) as u64),
            Int::Signed(n) => Int::Unsigned((*n == 0) as u64),
        }
    }

    #[inline(always)]
    fn bitneg(&mut self) {
        *self = match self {
            Int::Unsigned(n) => Int::Unsigned(!*n),
            Int::Signed(n) => Int::Signed(!*n),
        }
    }

    #[inline(always)]
    fn mul(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x * y),
                Int::Signed(y) => Int::Signed((*x as i64) * y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x * (y as i64)),
                Int::Signed(y) => Int::Signed(*x * y),
            },
        }
    }

    #[inline(always)]
    fn div(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x / y),
                Int::Signed(y) => Int::Signed((*x as i64) / y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x / (y as i64)),
                Int::Signed(y) => Int::Signed(*x / y),
            },
        }
    }

    #[inline(always)]
    fn modulo(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x % y),
                Int::Signed(y) => Int::Signed((*x as i64) % y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x % (y as i64)),
                Int::Signed(y) => Int::Signed(*x % y),
            },
        }
    }

    #[inline(always)]
    fn add(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x + y),
                Int::Signed(y) => Int::Signed((*x as i64) + y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x + (y as i64)),
                Int::Signed(y) => Int::Signed(*x + y),
            },
        }
    }

    #[inline(always)]
    fn sub(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => {
                    if *x >= y {
                        Int::Unsigned(*x - y)
                    } else {
                        Int::Signed(-((y - *x) as i64))
                    }
                }
                Int::Signed(y) => Int::Signed((*x as i64) - y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x - (y as i64)),
                Int::Signed(y) => Int::Signed(*x - y),
            },
        }
    }

    #[inline(always)]
    fn lshift(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x << y),
                Int::Signed(y) => Int::Signed((*x as i64) << y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x << (y as i64)),
                Int::Signed(y) => Int::Signed(*x << y),
            },
        }
    }

    #[inline(always)]
    fn rshift(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x >> y),
                Int::Signed(y) => Int::Signed((*x as i64) >> y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x >> (y as i64)),
                Int::Signed(y) => Int::Signed(*x >> y),
            },
        }
    }

    #[inline(always)]
    fn lt(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x < y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) < y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x < (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x < y) as u64),
            },
        }
    }

    #[inline(always)]
    fn gt(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x > y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) > y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x > (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x > y) as u64),
            },
        }
    }

    #[inline(always)]
    fn leq(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x <= y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) <= y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x <= (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x <= y) as u64),
            },
        }
    }

    #[inline(always)]
    fn geq(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x >= y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) >= y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x >= (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x >= y) as u64),
            },
        }
    }

    #[inline(always)]
    fn eq(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x == y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) == y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x == (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x == y) as u64),
            },
        }
    }

    #[inline(always)]
    fn neq(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x != y) as u64),
                Int::Signed(y) => Int::Unsigned(((*x as i64) != y) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned((*x != (y as i64)) as u64),
                Int::Signed(y) => Int::Unsigned((*x != y) as u64),
            },
        }
    }

    #[inline(always)]
    fn bitand(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x & y),
                Int::Signed(y) => Int::Signed((*x as i64) & y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x & (y as i64)),
                Int::Signed(y) => Int::Signed(*x & y),
            },
        }
    }

    #[inline(always)]
    fn bitxor(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x ^ y),
                Int::Signed(y) => Int::Signed((*x as i64) ^ y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x ^ (y as i64)),
                Int::Signed(y) => Int::Signed(*x ^ y),
            },
        }
    }

    #[inline(always)]
    fn bitor(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(*x | y),
                Int::Signed(y) => Int::Signed((*x as i64) | y),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Signed(*x | (y as i64)),
                Int::Signed(y) => Int::Signed(*x | y),
            },
        }
    }

    #[inline(always)]
    fn and(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(((*x != 0) && (y != 0)) as u64),
                Int::Signed(y) => Int::Unsigned(((*x != 0) && (y != 0)) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(((*x != 0) && (y != 0)) as u64),
                Int::Signed(y) => Int::Unsigned(((*x != 0) && (y != 0)) as u64),
            },
        }
    }

    #[inline(always)]
    fn or(&mut self, right: Int) {
        *self = match self {
            Int::Unsigned(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(((*x != 0) || (y != 0)) as u64),
                Int::Signed(y) => Int::Unsigned(((*x != 0) || (y != 0)) as u64),
            },
            Int::Signed(x) => match right {
                Int::Unsigned(y) => Int::Unsigned(((*x != 0) || (y != 0)) as u64),
                Int::Signed(y) => Int::Unsigned(((*x != 0) || (y != 0)) as u64),
            },
        }
    }
}

#[inline(always)]
fn precedence(op: Operator) -> (u32, Associativity) {
    use Operator::*;

    match op {
        Plus | Minus | Not | BitNeg => (2, Associativity::RL),
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
        _ => (0, Associativity::LR),
    }
}

#[inline(always)]
fn check_precedence(left: Operator, right: Operator) -> bool {
    // a + b * c => prec(*) < prec(+) so * has precedence on +
    let (l_prec, l_assoc) = precedence(left);
    let (r_prec, _) = precedence(right);

    if l_prec == r_prec {
        l_assoc == Associativity::LR
    } else {
        l_prec < r_prec
    }
}

pub struct Condition<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    operands: Vec<Int>,
    operators: Vec<Operator>,
    last: LastKind,
}

impl<'a, 'b, PC: PreprocContext> Condition<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self {
            lexer,
            operands: Vec::with_capacity(16),
            operators: Vec::with_capacity(16),
            last: LastKind::Operator,
        }
    }

    #[inline(always)]
    fn push_operator(&mut self, op: Operator) {
        loop {
            if let Some(top) = self.operators.last() {
                if *top != Operator::Parenthesis && check_precedence(*top, op) {
                    let top = self.operators.pop().unwrap();
                    top.operate(&mut self.operands);
                    continue;
                }
            }
            break;
        }
        self.last = LastKind::Operator;
        self.operators.push(op);
    }

    #[inline(always)]
    fn flush(&mut self) {
        while let Some(op) = self.operators.pop() {
            op.operate(&mut self.operands);
        }
    }

    #[inline(always)]
    fn flush_until_paren(&mut self) {
        while let Some(op) = self.operators.pop() {
            match op {
                Operator::Parenthesis => {
                    break;
                }
                _ => {
                    op.operate(&mut self.operands);
                }
            }
        }
    }

    #[inline(always)]
    fn handle_id(&mut self, id: &str) {
        if id == "defined" {
            let x = self.lexer.get_defined();
            self.operands.push(Int::Unsigned(x));
        } else {
            self.operands.push(Int::Unsigned(0));
        }
        self.last = LastKind::Operand;
    }

    fn eval(&mut self) -> Int {
        loop {
            let tok = self.lexer.next();
            match tok.tok {
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
                Token::EqualEqual => {
                    self.push_operator(Operator::Eq);
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
                Token::LiteralChar(x)
                | Token::LiteralLChar(x)
                | Token::LiteralUUChar(x)
                | Token::LiteralUChar(x)
                | Token::LiteralU8Char(x) => {
                    self.operands.push(Int::Unsigned(x as u64));
                    self.last = LastKind::Operand;
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
                Token::LeftParen => {
                    self.operators.push(Operator::Parenthesis);
                    self.last = LastKind::Operator;
                }
                Token::RightParen => {
                    self.flush_until_paren();
                }
                Token::LiteralInt(x)
                | Token::LiteralUInt(x)
                | Token::LiteralLong(x)
                | Token::LiteralLongLong(x)
                | Token::LiteralULong(x)
                | Token::LiteralULongLong(x) => {
                    self.operands.push(Int::Unsigned(x));
                    self.last = LastKind::Operand;
                }
                Token::Identifier(id) => {
                    self.handle_id(&id);
                }
                Token::AndKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::And);
                    } else {
                        self.handle_id("and");
                    }
                }
                Token::OrKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Or);
                    } else {
                        self.handle_id("or");
                    }
                }
                Token::BitAnd => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitAnd);
                    } else {
                        self.handle_id("bitand");
                    }
                }
                Token::BitOr => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitOr);
                    } else {
                        self.handle_id("bitxor");
                    }
                }
                Token::XorKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitXor);
                    } else {
                        self.handle_id("bitor");
                    }
                }
                Token::NotEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Neq);
                    } else {
                        self.handle_id("not_eq");
                    }
                }
                Token::NotKw => {
                    // TODO: this is not correct
                    // we need to check next token to decide
                    self.push_operator(Operator::Not);
                }
                Token::Compl => {
                    // TODO: this is not correct
                    // we need to check next token to decide
                    self.push_operator(Operator::BitNeg);
                }
                Token::True => {
                    self.handle_id("true");
                }
                Token::False => {
                    self.handle_id("false");
                }
                Token::Comment(_) => {}
                Token::Question => {
                    self.push_operator(Operator::Question);
                }
                Token::Colon => {
                    self.push_operator(Operator::Colon);
                }
                Token::Eol | Token::Eof => {
                    self.flush();
                    return self.operands.pop().unwrap();
                }
                _ => {
                    unreachable!(
                        "Got token {:?} at line {} in file {:?}",
                        tok.tok,
                        tok.start.line,
                        self.lexer
                            .context
                            .get_path(self.lexer.buf.get_source_id().unwrap())
                    );
                }
            }
        }
    }

    pub(crate) fn eval_as_bool(&mut self) -> bool {
        match self.eval() {
            Int::Unsigned(x) => x != 0,
            Int::Signed(x) => x != 0,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_condition_base() {
        let mut lexer = Lexer::<DefaultContext>::new(b"1\n");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));
    }

    #[test]
    fn test_condition_add() {
        let mut lexer = Lexer::<DefaultContext>::new(b"2 + 3");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(5));
    }

    #[test]
    fn test_condition_mul() {
        let mut lexer = Lexer::<DefaultContext>::new(b"2 * 3");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(6));
    }

    #[test]
    fn test_condition_prec() {
        let mut lexer = Lexer::<DefaultContext>::new(b"2 + 3 * 4");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(14));
    }

    #[test]
    fn test_condition_prec_log() {
        let mut lexer = Lexer::<DefaultContext>::new(b"1 && 0 || 1");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));
    }

    #[test]
    fn test_condition_signed() {
        let mut lexer = Lexer::<DefaultContext>::new(b"-1 + (2 * 3 - 4) /* a comment */ * -3");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Signed(-7));
    }

    #[test]
    fn test_condition_comment() {
        let mut lexer = Lexer::<DefaultContext>::new(b"-1 + (2 * 3 - 4) // comment\n");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Signed(1));
    }

    #[test]
    fn test_condition_and() {
        let mut lexer = Lexer::<DefaultContext>::new(b"1 and 2");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));
    }

    #[test]
    fn test_condition_not_not() {
        let mut lexer = Lexer::<DefaultContext>::new(b"!!1");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));
    }

    #[test]
    fn test_condition_macro() {
        let mut lexer = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo 1\n",
                "#define bar 1\n",
                "foo && bar\n",
                "foo || !bar\n",
            )
            .as_bytes(),
        );
        lexer.consume_tokens(2);

        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));

        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(1));
    }

    #[test]
    fn test_question() {
        let mut lexer = Lexer::<DefaultContext>::new(b"1 ? 2 : 3");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(2));

        let mut lexer = Lexer::<DefaultContext>::new(b"0 ? 2 : 3");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(3));

        let mut lexer = Lexer::<DefaultContext>::new(b"0 * 1 ? 2 * 3 : 3 * 4");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(12));

        let mut lexer = Lexer::<DefaultContext>::new(b"1 + 1 ? 2 * 3 : 3 * 4");
        let mut cond = Condition::new(&mut lexer);
        let res = cond.eval();

        assert_eq!(res, Int::Unsigned(6));
    }
}
