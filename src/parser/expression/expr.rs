use super::list::{ListInitialization, ListInitializationParser};
use super::operator::{BinaryOp, Operator, UnaryOp};
use super::params::{Parameters, ParametersParser};
use crate::lexer::lexer::{Lexer, LocToken, Token};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::parser::literals::{
    Bool, Char, CharLiteral, Float, FloatLiteral, IntLiteral, Integer, Nullptr, Str, StrLiteral,
};
use crate::parser::name::{Qualified, QualifiedParser};
//use crate::dump::Dump;

#[derive(Clone, Debug, PartialEq)]
pub enum ExprNode {
    UnaryOp(Box<UnaryOp>),
    BinaryOp(Box<BinaryOp>),
    CallExpr(Box<CallExpr>),
    Qualified(Box<Qualified>),
    ListInit(Box<ListInitialization>),
    InitExpr(Box<InitExpr>),
    Integer(Box<Integer>),
    Float(Box<Float>),
    Char(Box<Char>),
    Str(Box<Str>),
    Bool(Box<Bool>),
    Nullptr(Box<Nullptr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallExpr {
    pub callee: ExprNode,
    pub params: Parameters,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitExpr {
    pub base: ExprNode,
    pub list: ListInitialization,
}

#[derive(PartialEq)]
enum LastKind {
    Operator,
    Operand,
}

#[derive(PartialEq)]
enum Associativity {
    LR,
    RL,
}

#[inline(always)]
fn precedence(op: Operator) -> (u32, Associativity) {
    use Operator::*;

    match op {
        ScopeResolution => (1, Associativity::LR),
        PostInc | PostDec | Call | Dot | Arrow | Subscript => (2, Associativity::LR),
        PreInc | PreDec | Plus | Minus | Indirection | AddressOf | Not | BitNeg | Sizeof | New
        | NewArray | Delete | DeleteArray | CoAwait => (3, Associativity::RL),
        DotIndirection | ArrowIndirection => (4, Associativity::LR),
        Mul | Div | Mod => (5, Associativity::LR),
        Add | Sub => (6, Associativity::LR),
        LShift | RShift => (7, Associativity::LR),
        ThreeWayComp => (8, Associativity::LR),
        Lt | Gt | Leq | Geq => (9, Associativity::LR),
        Eq | Neq => (10, Associativity::LR),
        BitAnd => (11, Associativity::LR),
        BitXor => (12, Associativity::LR),
        BitOr => (13, Associativity::LR),
        And => (14, Associativity::LR),
        Or => (15, Associativity::LR),
        Question | Colon | Throw | CoYield | Assign | AddAssign | SubAssign | MulAssign
        | DivAssign | ModAssign | LShiftAssign | RShiftAssign | AndAssign | XorAssign
        | OrAssign => (16, Associativity::RL),
        Comma => (17, Associativity::LR),
        Parenthesis => (0, Associativity::LR),
    }
}

#[inline(always)]
fn check_precedence(left: Operator, right: Operator) -> bool {
    // TODO: replace this by a table
    // a + b * c => prec(+) <= prec(*) is true so * has precedence on +
    let (l_prec, l_assoc) = precedence(left);
    let (r_prec, _) = precedence(right);

    if l_prec == r_prec {
        l_assoc == Associativity::LR
    } else {
        l_prec < r_prec
    }
}

pub struct ExpressionParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
    operands: Vec<ExprNode>,
    operators: Vec<Operator>,
    last: LastKind,
    term: Token<'a>,
}

impl<'a, 'b, PC: PreprocContext> ExpressionParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>, term: Token<'a>) -> Self {
        Self {
            lexer,
            operands: Vec::new(),
            operators: Vec::new(),
            last: LastKind::Operator,
            term,
        }
    }

    fn push_operator(&mut self, op: Operator) {
        self.flush_with_op(op);
        self.last = LastKind::Operator;
        self.operators.push(op);
    }

    fn flush_with_op(&mut self, op: Operator) {
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
    }

    fn flush(&mut self) {
        while let Some(op) = self.operators.pop() {
            op.operate(&mut self.operands);
        }
    }

    fn get_node(&mut self) -> Option<ExprNode> {
        self.flush();
        self.operands.pop()
    }

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

    fn is_nested(&mut self) -> bool {
        self.operators.contains(&Operator::Parenthesis)
    }

    fn is_terminal(&mut self, tok: Token<'a>) -> bool {
        self.term == tok || tok == Token::RightParen && !self.is_nested()
    }

    fn handle_id(&mut self, id: String) -> LocToken<'a> {
        let qp = QualifiedParser::new(self.lexer);
        let (tk, qual) = qp.parse(None, Some(id));

        self.operands
            .push(ExprNode::Qualified(Box::new(qual.unwrap())));
        self.last = LastKind::Operand;

        tk.unwrap_or_else(|| self.lexer.next_useful())
    }

    pub(crate) fn parse_with_id(
        &mut self,
        tok: Option<LocToken<'a>>,
        name: Qualified,
    ) -> (Option<LocToken<'a>>, Option<ExprNode>) {
        self.operands.push(ExprNode::Qualified(Box::new(name)));
        self.last = LastKind::Operand;

        self.parse(tok)
    }

    pub(crate) fn parse(
        &mut self,
        tok: Option<LocToken<'a>>,
    ) -> (Option<LocToken<'a>>, Option<ExprNode>) {
        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        loop {
            match tok.tok {
                Token::Plus => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Add);
                    } else {
                        self.push_operator(Operator::Plus);
                    }
                }
                Token::PlusPlus => {
                    if self.last == LastKind::Operand {
                        self.flush_with_op(Operator::PostInc);
                        let arg = self.operands.pop().unwrap();
                        self.operands.push(ExprNode::UnaryOp(Box::new(UnaryOp {
                            op: Operator::PostInc,
                            arg,
                        })));
                        self.last = LastKind::Operand;
                    } else {
                        self.push_operator(Operator::PreInc);
                    }
                }
                Token::Minus => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Sub);
                    } else {
                        self.push_operator(Operator::Minus);
                    }
                }
                Token::MinusMinus => {
                    if self.last == LastKind::Operand {
                        self.flush_with_op(Operator::PostDec);
                        let arg = self.operands.pop().unwrap();
                        self.operands.push(ExprNode::UnaryOp(Box::new(UnaryOp {
                            op: Operator::PostDec,
                            arg,
                        })));
                        self.last = LastKind::Operand;
                    } else {
                        self.push_operator(Operator::PreDec);
                    }
                }
                Token::Sizeof => {
                    let tk = self.lexer.next_useful();
                    if tk.tok == Token::LeftParen {
                        let pp = ParametersParser::new(self.lexer, Token::RightParen);
                        let (_, params) = pp.parse(None);
                        self.operands.push(ExprNode::UnaryOp(Box::new(UnaryOp {
                            op: Operator::Sizeof,
                            arg: params.unwrap().pop().unwrap().unwrap(),
                        })));
                        self.last = LastKind::Operand;
                    } else {
                        self.push_operator(Operator::Sizeof);
                    }
                }
                Token::Arrow => {
                    self.push_operator(Operator::Arrow);
                }
                Token::Dot => {
                    self.push_operator(Operator::Dot);
                }
                Token::Not => {
                    self.push_operator(Operator::Not);
                }
                Token::NotKw => {
                    if self.last == LastKind::Operand {
                        tok = self.handle_id("not".to_string());
                        continue;
                    } else {
                        self.push_operator(Operator::Not);
                    }
                }
                Token::Tilde => {
                    self.push_operator(Operator::BitNeg);
                }
                Token::Compl => {
                    if self.last == LastKind::Operand {
                        tok = self.handle_id("compl".to_string());
                        continue;
                    } else {
                        self.push_operator(Operator::BitNeg);
                    }
                }
                Token::Star => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Mul);
                    } else {
                        self.push_operator(Operator::Indirection);
                    }
                }
                Token::DotStar => {
                    self.push_operator(Operator::DotIndirection);
                }
                Token::ArrowStar => {
                    self.push_operator(Operator::ArrowIndirection);
                }
                Token::Divide => {
                    self.push_operator(Operator::Div);
                }
                Token::Modulo => {
                    self.push_operator(Operator::Mod);
                }
                Token::LeftBrack => {
                    if self.last == LastKind::Operand {
                        self.flush_with_op(Operator::Subscript);
                        let mut ep = ExpressionParser::new(&mut self.lexer, Token::RightBrack);
                        let (tk, expr) = ep.parse(None);
                        if tk.map_or(true, |t| t.tok == Token::RightBrack) {
                            let array = self.operands.pop().unwrap();
                            self.operands.push(ExprNode::BinaryOp(Box::new(BinaryOp {
                                op: Operator::Subscript,
                                arg1: array,
                                arg2: expr.unwrap(),
                            })));
                        } else {
                            unreachable!("Wrong token in array dimension");
                        }
                    } else {
                        // TODO: lambda: https://en.cppreference.com/w/cpp/language/lambda
                    }
                    self.last = LastKind::Operand;
                }
                Token::LeftShift => {
                    self.push_operator(Operator::LShift);
                }
                Token::RightShift => {
                    if self.is_terminal(Token::Greater) {
                        let mut tok = tok.clone();
                        tok.tok = Token::Greater;
                        tok.start.column += 1;
                        return (Some(tok), self.get_node());
                    } else {
                        self.push_operator(Operator::RShift);
                    }
                }
                Token::Lower => {
                    self.push_operator(Operator::Lt);
                }
                Token::LowerEqualGreater => {
                    self.push_operator(Operator::ThreeWayComp);
                }
                Token::Greater => {
                    if self.is_terminal(Token::Greater) {
                        return (Some(tok), self.operands.pop());
                    } else {
                        self.push_operator(Operator::Gt);
                    }
                }
                Token::LowerEqual => {
                    self.push_operator(Operator::Leq);
                }
                Token::GreaterEqual => {
                    if self.is_terminal(Token::Greater) {
                        let mut tok = tok.clone();
                        tok.tok = Token::Equal;
                        tok.start.column += 1;
                        return (Some(tok), self.get_node());
                    } else {
                        self.push_operator(Operator::Geq);
                    }
                }
                Token::NotEqual => {
                    self.push_operator(Operator::Neq);
                }
                Token::NotEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Neq);
                    } else {
                        tok = self.handle_id("not_eq".to_string());
                        continue;
                    }
                }
                Token::And => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitAnd);
                    } else {
                        self.push_operator(Operator::AddressOf);
                    }
                }
                Token::BitAnd => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitAnd);
                    } else {
                        tok = self.handle_id("bitand".to_string());
                        continue;
                    }
                }
                Token::Xor => {
                    self.push_operator(Operator::BitXor);
                }
                Token::XorKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitXor);
                    } else {
                        tok = self.handle_id("xor".to_string());
                        continue;
                    }
                }
                Token::Or => {
                    self.push_operator(Operator::BitOr);
                }
                Token::BitOr => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::BitOr);
                    } else {
                        tok = self.handle_id("bitor".to_string());
                        continue;
                    }
                }
                Token::AndAnd => {
                    self.push_operator(Operator::And);
                }
                Token::AndKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::And);
                    } else {
                        tok = self.handle_id("and".to_string());
                        continue;
                    }
                }
                Token::OrOr => {
                    self.push_operator(Operator::Or);
                }
                Token::OrKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Or);
                    } else {
                        tok = self.handle_id("or".to_string());
                        continue;
                    }
                }
                Token::Question => {
                    self.push_operator(Operator::Question);
                }
                Token::Colon => {
                    self.push_operator(Operator::Colon);
                }
                Token::LeftParen => {
                    if self.last == LastKind::Operand {
                        // We've a call
                        self.flush_with_op(Operator::Call);
                        let pp = ParametersParser::new(self.lexer, Token::RightParen);
                        let (_, params) = pp.parse(None);
                        let callee = self.operands.pop().unwrap();
                        self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                            callee,
                            params: params.unwrap(),
                        })));
                        self.last = LastKind::Operand;
                    } else {
                        self.operators.push(Operator::Parenthesis);
                        self.last = LastKind::Operator;
                    }
                }
                Token::LeftBrace => {
                    let lip = ListInitializationParser::new(self.lexer);
                    let (_, list) = lip.parse(Some(tok));
                    if self.last == LastKind::Operand {
                        // We've an initialization
                        self.flush_with_op(Operator::Call);
                        let base = self.operands.pop().unwrap();
                        self.operands.push(ExprNode::InitExpr(Box::new(InitExpr {
                            base,
                            list: list.unwrap(),
                        })));
                    } else {
                        // Initializer-list
                        self.operands
                            .push(ExprNode::ListInit(Box::new(list.unwrap())));
                    }
                    self.last = LastKind::Operand;
                }
                Token::Comma => {
                    if self.is_nested() {
                        self.push_operator(Operator::Comma);
                    } else {
                        return (Some(tok), self.get_node());
                    }
                }
                Token::RightParen => {
                    if self.is_terminal(Token::RightParen) {
                        return (Some(tok), self.get_node());
                    } else {
                        self.flush_until_paren();
                    }
                }
                Token::Equal => {
                    self.push_operator(Operator::Assign);
                }
                Token::PlusEqual => {
                    self.push_operator(Operator::AddAssign);
                }
                Token::MinusEqual => {
                    self.push_operator(Operator::SubAssign);
                }
                Token::StarEqual => {
                    self.push_operator(Operator::MulAssign);
                }
                Token::DivideEqual => {
                    self.push_operator(Operator::DivAssign);
                }
                Token::ModuloEqual => {
                    self.push_operator(Operator::ModAssign);
                }
                Token::LeftShiftEqual => {
                    self.push_operator(Operator::LShiftAssign);
                }
                Token::RightShiftEqual => {
                    self.push_operator(Operator::RShiftAssign);
                }
                Token::AndEqual => {
                    self.push_operator(Operator::AndAssign);
                }
                Token::AndEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::AndAssign);
                    } else {
                        tok = self.handle_id("and_eq".to_string());
                        continue;
                    }
                }
                Token::XorEqual => {
                    self.push_operator(Operator::XorAssign);
                }
                Token::XorEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::XorAssign);
                    } else {
                        tok = self.handle_id("xor_eq".to_string());
                        continue;
                    }
                }
                Token::OrEqual => {
                    self.push_operator(Operator::OrAssign);
                }
                Token::OrEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::OrAssign);
                    } else {
                        tok = self.handle_id("or_eq".to_string());
                        continue;
                    }
                }
                Token::Identifier(id) => {
                    tok = self.handle_id(id);
                    continue;
                }
                Token::LiteralChar(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::Char(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLChar(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::LChar(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUUChar(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::UUChar(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUChar(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::UChar(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralU8Char(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::U8Char(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralDouble(x) => {
                    self.operands.push(ExprNode::Float(Box::new(Float {
                        value: FloatLiteral::Double(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralFloat(x) => {
                    self.operands.push(ExprNode::Float(Box::new(Float {
                        value: FloatLiteral::Float(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLongDouble(x) => {
                    self.operands.push(ExprNode::Float(Box::new(Float {
                        value: FloatLiteral::LongDouble(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralInt(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::Int(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUInt(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::UInt(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLong(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::Long(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralULong(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::ULong(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLongLong(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::LongLong(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralULongLong(x) => {
                    self.operands.push(ExprNode::Integer(Box::new(Integer {
                        value: IntLiteral::ULongLong(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::Str(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::LStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::UStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUUString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::UUStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralU8String(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::U8Str(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralRString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::RStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLRString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::LRStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralURString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::URStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUURString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::UURStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralU8RString(x) => {
                    self.operands.push(ExprNode::Str(Box::new(Str {
                        value: StrLiteral::U8RStr(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::Nullptr => {
                    self.operands.push(ExprNode::Nullptr(Box::new(Nullptr {})));
                    self.last = LastKind::Operand;
                }
                Token::True => {
                    self.operands
                        .push(ExprNode::Bool(Box::new(Bool { value: true })));
                    self.last = LastKind::Operand;
                }
                Token::False => {
                    self.operands
                        .push(ExprNode::Bool(Box::new(Bool { value: false })));
                    self.last = LastKind::Operand;
                }
                _ => {
                    //eprintln!("COUCOU {:?}\n{:?}\n", self.operands, self.operators);
                    return (Some(tok), self.get_node());
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::name::*;
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_add_associativity() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a + (b + c)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Add,
                arg1: ExprNode::Qualified(Box::new(mk_id!("b"))),
                arg2: ExprNode::Qualified(Box::new(mk_id!("c"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_priority() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a + b * c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Mul,
                arg1: ExprNode::Qualified(Box::new(mk_id!("b"))),
                arg2: ExprNode::Qualified(Box::new(mk_id!("c"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_priority_2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a * b + c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(BinaryOp {
                op: Operator::Mul,
                arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
            }),
            arg2: ExprNode::Qualified(Box::new(mk_id!("c"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_call() {
        let mut lexer = Lexer::<DefaultContext>::new(b"foo::bar(a, b)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Qualified(Box::new(mk_id!("foo", "bar"))),
            params: vec![
                Some(ExprNode::Qualified(Box::new(mk_id!("a")))),
                Some(ExprNode::Qualified(Box::new(mk_id!("b")))),
            ],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_sizeof() {
        let mut lexer = Lexer::<DefaultContext>::new(b"sizeof(A)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::Sizeof,
            arg: ExprNode::Qualified(Box::new(mk_id!("A"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_array() {
        let mut lexer = Lexer::<DefaultContext>::new(b"abc[x]");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Subscript,
            arg1: ExprNode::Qualified(Box::new(mk_id!("abc"))),
            arg2: ExprNode::Qualified(Box::new(mk_id!("x"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_arrow_plus() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a->b(c) + d");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(CallExpr {
                callee: node!(BinaryOp {
                    op: Operator::Arrow,
                    arg1: ExprNode::Qualified(Box::new(mk_id!("a"))),
                    arg2: ExprNode::Qualified(Box::new(mk_id!("b"))),
                }),
                params: vec![Some(ExprNode::Qualified(Box::new(mk_id!("c")))),],
            }),
            arg2: ExprNode::Qualified(Box::new(mk_id!("d"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_pre_post_inc() {
        let mut lexer = Lexer::<DefaultContext>::new(b"++a++");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::PreInc,
            arg: node!(UnaryOp {
                op: Operator::PostInc,
                arg: ExprNode::Qualified(Box::new(mk_id!("a"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_ind_post_inc() {
        let mut lexer = Lexer::<DefaultContext>::new(b"*p++");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let node = parser.parse(None).1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::Indirection,
            arg: node!(UnaryOp {
                op: Operator::PostInc,
                arg: ExprNode::Qualified(Box::new(mk_id!("p"))),
            }),
        });

        assert_eq!(node, expected);
    }
}
