// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::rc::Rc;
use termcolor::StandardStreamLock;

use super::list::{ListInitialization, ListInitializationParser};
use super::operator::{BinaryOp, Conditional, Operator, UnaryOp};
use super::params::{Parameters, ParametersParser};
use crate::lexer::lexer::{TLexer, Token};
use crate::parser::context::{Context, SearchResult, TypeToFix};
use crate::parser::declarations::{DeclSpecifierParser, TypeDeclarator};
use crate::parser::dump::Dump;
use crate::parser::errors::ParserError;
use crate::parser::literals::{
    Bool, Char, CharLiteral, Float, FloatLiteral, IntLiteral, Integer, Str, StrLiteral,
    StringLiteralParser,
};
use crate::parser::names::{Qualified, QualifiedParser};
use crate::parser::types::Type;

#[derive(Clone, Debug, PartialEq)]
pub struct Nullptr {}

impl ToString for Nullptr {
    fn to_string(&self) -> String {
        "nullptr".to_string()
    }
}

impl Dump for Nullptr {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct This {}

impl ToString for This {
    fn to_string(&self) -> String {
        "this".to_string()
    }
}

impl Dump for This {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self.to_string(), prefix, last, stdout);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum VarDecl {
    Direct(Rc<TypeDeclarator>),
    Indirect(TypeToFix),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Variable {
    pub name: Qualified,
    pub decl: VarDecl,
}

impl Dump for Variable {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "variable", prefix, last, stdout, name, decl);
    }
}

impl Dump for VarDecl {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        // TODO: fix me
        match self {
            Self::Direct(_) => dump_str!(name, "<direct>", Cyan, prefix, last, stdout),
            Self::Indirect(i) => i.dump(name, prefix, last, stdout),
        };
    }
}

#[macro_export]
macro_rules! mk_var {
    ( $( $name:expr ),* ) => {
        crate::parser::expressions::expr::Variable {
            name: mk_id!($( $name ),*),
            decl: crate::parser::expressions::expr::VarDecl::Indirect(crate::parser::context::TypeToFix::default()),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprNode {
    UnaryOp(Box<UnaryOp>),
    BinaryOp(Box<BinaryOp>),
    Conditional(Box<Conditional>),
    CallExpr(Box<CallExpr>),
    Variable(Box<Variable>),
    ListInit(Box<ListInitialization>),
    InitExpr(Box<InitExpr>),
    Integer(Box<Integer>),
    Float(Box<Float>),
    Char(Box<Char>),
    Str(Box<Str>),
    Bool(Box<Bool>),
    Nullptr(Box<Nullptr>),
    This(Box<This>),
    Type(Box<Type>),
}

impl Dump for ExprNode {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        macro_rules! dump {
            ( $x: ident) => {
                $x.dump(name, prefix, last, stdout)
            };
        }

        match self {
            Self::UnaryOp(x) => dump!(x),
            Self::BinaryOp(x) => dump!(x),
            Self::Conditional(x) => dump!(x),
            Self::CallExpr(x) => dump!(x),
            Self::Variable(x) => dump!(x),
            Self::ListInit(x) => dump!(x),
            Self::InitExpr(x) => dump!(x),
            Self::Integer(x) => dump!(x),
            Self::Float(x) => dump!(x),
            Self::Char(x) => dump!(x),
            Self::Str(x) => dump!(x),
            Self::Bool(x) => dump!(x),
            Self::Nullptr(x) => dump!(x),
            Self::This(x) => dump!(x),
            Self::Type(x) => dump!(x),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CallExpr {
    pub callee: ExprNode,
    pub params: Parameters,
}

impl Dump for CallExpr {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "call", prefix, last, stdout, callee, params);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct InitExpr {
    pub base: ExprNode,
    pub list: ListInitialization,
}

impl Dump for InitExpr {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_obj!(self, name, "init", prefix, last, stdout, base, list);
    }
}

#[derive(PartialEq)]
pub(super) enum LastKind {
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
        Parenthesis => (0, Associativity::LR),
        ScopeResolution => (1, Associativity::LR),
        PostInc | PostDec | Call | Dot | Arrow | Subscript => (2, Associativity::LR),
        PreInc | PreDec | Plus | Minus | Indirection | AddressOf | AddressOfLabel | Not
        | BitNeg | Sizeof | New | NewArray | Delete | DeleteArray | CoAwait | Cast => {
            (3, Associativity::RL)
        }
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
        Conditional | Throw | CoYield | Assign | AddAssign | SubAssign | MulAssign | DivAssign
        | ModAssign | LShiftAssign | RShiftAssign | AndAssign | XorAssign | OrAssign => {
            (16, Associativity::RL)
        }
        Comma => (17, Associativity::LR),
    }
}

#[inline(always)]
fn check_precedence(left: Operator, right: Operator) -> bool {
    // TODO: replace this by a table
    // a + b * c => prec(*) < prec(+) is true so * has precedence on +
    let (l_prec, l_assoc) = precedence(left);
    let (r_prec, _) = precedence(right);

    if l_prec == r_prec {
        l_assoc == Associativity::LR
    } else {
        l_prec < r_prec
    }
}

pub struct ExpressionParser<'a, L: TLexer> {
    pub(super) lexer: &'a mut L,
    pub(super) operands: Vec<ExprNode>,
    pub(super) operators: Vec<Operator>,
    pub(super) last: LastKind,
    pub(super) term: Token,
    pub(super) level: usize,
}

impl<'a, L: TLexer> ExpressionParser<'a, L> {
    pub(crate) fn new(lexer: &'a mut L, term: Token) -> Self {
        Self {
            lexer,
            operands: Vec::new(),
            operators: Vec::new(),
            last: LastKind::Operator,
            term,
            level: 0,
        }
    }

    pub(crate) fn push_operator(&mut self, op: Operator) {
        self.flush_with_op(op);
        self.operators.push(op);
        self.last = LastKind::Operator;
    }

    pub(crate) fn push_operand(&mut self, op: ExprNode) {
        self.operands.push(op);
        self.last = LastKind::Operand;
    }

    pub(super) fn flush_with_op(&mut self, op: Operator) {
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

    pub(super) fn flush(&mut self) {
        while let Some(op) = self.operators.pop() {
            op.operate(&mut self.operands);
        }
    }

    pub(crate) fn get_node(&mut self) -> Option<ExprNode> {
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

    fn is_terminal(&mut self, tok: Token) -> bool {
        self.term == tok || (tok == Token::RightParen && !self.is_nested())
    }

    fn handle_id(&mut self, id: String, context: &mut Context) -> Result<Token, ParserError> {
        let qp = QualifiedParser::new(self.lexer);
        let (tk, qual) = qp.parse(None, Some(id), context)?;

        self.handle_qual(qual, context)?;
        Ok(tk.unwrap_or_else(|| self.lexer.next_useful()))
    }

    fn handle_qual(
        &mut self,
        qual: Option<Qualified>,
        context: &mut Context,
    ) -> Result<(), ParserError> {
        let decl = if let Some(res) = context.search(qual.as_ref()) {
            match res {
                SearchResult::Var(var) => VarDecl::Direct(var),
                SearchResult::Type(_) | SearchResult::IncompleteType(_) => {
                    return Err(ParserError::InvalidTypeInExpr {
                        sp: self.lexer.span(),
                        name: qual.unwrap().to_string(),
                    });
                }
                SearchResult::IncompleteVar(var) => {
                    // Can happen with self referring functions
                    VarDecl::Indirect(var)
                }
            }
        } else {
            VarDecl::Indirect(TypeToFix::default())
        };

        self.operands.push(ExprNode::Variable(Box::new(Variable {
            name: qual.unwrap(),
            decl,
        })));
        self.last = LastKind::Operand;

        Ok(())
    }

    pub(crate) fn parse_with_id(
        &mut self,
        tok: Option<Token>,
        name: Qualified,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<ExprNode>), ParserError> {
        self.handle_qual(Some(name), context)?;
        self.parse(tok, context)
    }

    pub(crate) fn parse(
        &mut self,
        tok: Option<Token>,
        context: &mut Context,
    ) -> Result<(Option<Token>, Option<ExprNode>), ParserError> {
        macro_rules! str_literal {
            ($s: expr, $name: ident) => {{
                let slp = StringLiteralParser::new(self.lexer);
                let (tk, x) = slp.parse(&$s, context)?;
                self.operands.push(ExprNode::Str(Box::new(Str {
                    value: StrLiteral::$name(x),
                })));
                self.last = LastKind::Operand;
                tk.unwrap_or_else(|| self.lexer.next_useful())
            }};
        }

        macro_rules! str_literal_ud {
            ($x: expr, $name: ident) => {{
                let slp = StringLiteralParser::new(self.lexer);
                let (tk, mut s) = slp.parse(&$x.0, context)?;
                std::mem::swap(&mut $x.0, &mut s);
                self.operands.push(ExprNode::Str(Box::new(Str {
                    value: StrLiteral::$name($x),
                })));
                self.last = LastKind::Operand;
                tk.unwrap_or_else(|| self.lexer.next_useful())
            }};
        }

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        loop {
            if tok == self.term && self.level == 0 {
                return Ok((Some(tok), self.get_node()));
            }

            match tok {
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
                    if tk == Token::LeftParen {
                        let pp = ParametersParser::new(self.lexer, Token::RightParen);
                        let (_, params) = pp.parse(None, None, context)?;
                        self.operands.push(ExprNode::UnaryOp(Box::new(UnaryOp {
                            op: Operator::Sizeof,
                            arg: params.unwrap().pop().unwrap(),
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
                        tok = self.handle_id("not".to_string(), context)?;
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
                        tok = self.handle_id("compl".to_string(), context)?;
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
                        let mut ep = ExpressionParser::new(self.lexer, Token::RightBrack);
                        let (tk, expr) = ep.parse(None, context)?;
                        if let Some(tk) = tk {
                            let array = self.operands.pop().unwrap();
                            self.operands.push(ExprNode::BinaryOp(Box::new(BinaryOp {
                                op: Operator::Subscript,
                                arg1: array,
                                arg2: expr.unwrap(),
                            })));
                            if tk == Token::DoubleRightBrack {
                                tok = Token::RightBrack;
                                continue;
                            }
                        }
                    } else {
                        // TODO: lambda: https://en.cppreference.com/w/cpp/language/lambda
                    }
                    self.last = LastKind::Operand;
                }
                Token::DoubleRightBrack => {
                    if self.is_terminal(Token::RightBrack) {
                        return Ok((Some(tok), self.get_node()));
                    }
                }
                Token::LeftShift => {
                    self.push_operator(Operator::LShift);
                }
                Token::RightShift => {
                    if self.is_terminal(Token::Greater) {
                        let tok = Token::Greater;
                        // TODO: fix token location in lexer
                        //tok.start.column += 1;
                        return Ok((Some(tok), self.get_node()));
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
                        return Ok((Some(tok), self.operands.pop()));
                    } else {
                        self.push_operator(Operator::Gt);
                    }
                }
                Token::LowerEqual => {
                    self.push_operator(Operator::Leq);
                }
                Token::GreaterEqual => {
                    if self.is_terminal(Token::Greater) {
                        let tok = Token::Equal;
                        // TODO: fix token location in lexer
                        //tok.start.column += 1;
                        return Ok((Some(tok), self.get_node()));
                    } else {
                        self.push_operator(Operator::Geq);
                    }
                }
                Token::NotEqual => {
                    self.push_operator(Operator::Neq);
                }
                Token::EqualEqual => {
                    self.push_operator(Operator::Eq);
                }
                Token::NotEq => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::Neq);
                    } else {
                        tok = self.handle_id("not_eq".to_string(), context)?;
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
                        tok = self.handle_id("bitand".to_string(), context)?;
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
                        tok = self.handle_id("xor".to_string(), context)?;
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
                        tok = self.handle_id("bitor".to_string(), context)?;
                        continue;
                    }
                }
                Token::AndAnd => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::And);
                    } else {
                        self.push_operator(Operator::AddressOfLabel);
                    }
                }
                Token::AndKw => {
                    if self.last == LastKind::Operand {
                        self.push_operator(Operator::And);
                    } else {
                        tok = self.handle_id("and".to_string(), context)?;
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
                        tok = self.handle_id("or".to_string(), context)?;
                        continue;
                    }
                }
                Token::Question => {
                    let mut ep = ExpressionParser::new(self.lexer, Token::Colon);
                    let (tok, expr) = ep.parse(None, context)?;
                    let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

                    if tok != Token::Colon {
                        return Err(ParserError::InvalidTokenInConditional {
                            sp: self.lexer.span(),
                            tok,
                        });
                    }

                    let left = expr.unwrap();
                    self.push_operator(Operator::Conditional);
                    self.operands.push(left);
                    self.last = LastKind::Operator;
                }
                Token::LeftParen => {
                    if self.last == LastKind::Operand {
                        // We've a call
                        self.flush_with_op(Operator::Call);
                        let pp = ParametersParser::new(self.lexer, Token::RightParen);
                        let (_, params) = pp.parse(None, None, context)?;
                        let callee = self.operands.pop().unwrap();
                        self.operands.push(ExprNode::CallExpr(Box::new(CallExpr {
                            callee,
                            params: params.unwrap(),
                        })));
                        self.last = LastKind::Operand;
                    } else {
                        let tk = self.parse_left_paren(context)?;
                        tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                        continue;
                    }
                }
                Token::LeftBrace => {
                    let lip = ListInitializationParser::new(self.lexer);
                    let (_, list) = lip.parse(Some(tok), context)?;
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
                    self.push_operator(Operator::Comma);
                }
                Token::RightParen => {
                    if self.level == 0 {
                        return Ok((Some(tok), self.get_node()));
                    }
                    self.level -= 1;
                    self.flush_until_paren();
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
                        tok = self.handle_id("and_eq".to_string(), context)?;
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
                        tok = self.handle_id("xor_eq".to_string(), context)?;
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
                        tok = self.handle_id("or_eq".to_string(), context)?;
                        continue;
                    }
                }
                Token::Final => {
                    tok = self.handle_id("final".to_string(), context)?;
                    continue;
                }
                Token::Import => {
                    tok = self.handle_id("import".to_string(), context)?;
                    continue;
                }
                Token::Module => {
                    tok = self.handle_id("module".to_string(), context)?;
                    continue;
                }
                Token::Override => {
                    tok = self.handle_id("override".to_string(), context)?;
                    continue;
                }
                Token::Identifier(id) => {
                    tok = self.handle_id(id, context)?;
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
                Token::LiteralCharUD(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::CharUD(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralLCharUD(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::LCharUD(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUUCharUD(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::UUCharUD(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralUCharUD(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::UCharUD(x),
                    })));
                    self.last = LastKind::Operand;
                }
                Token::LiteralU8CharUD(x) => {
                    self.operands.push(ExprNode::Char(Box::new(Char {
                        value: CharLiteral::U8CharUD(x),
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
                Token::LiteralFloatUD(x) => {
                    self.operands.push(ExprNode::Float(Box::new(Float {
                        value: FloatLiteral::FloatUD(x),
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
                    tok = str_literal!(x, Str);
                    continue;
                }
                Token::LiteralLString(x) => {
                    tok = str_literal!(x, LStr);
                    continue;
                }
                Token::LiteralUString(x) => {
                    tok = str_literal!(x, UStr);
                    continue;
                }
                Token::LiteralUUString(x) => {
                    tok = str_literal!(x, UUStr);
                    continue;
                }
                Token::LiteralU8String(x) => {
                    tok = str_literal!(x, U8Str);
                    continue;
                }
                Token::LiteralRString(x) => {
                    tok = str_literal!(x, RStr);
                    continue;
                }
                Token::LiteralLRString(x) => {
                    tok = str_literal!(x, LRStr);
                    continue;
                }
                Token::LiteralURString(x) => {
                    tok = str_literal!(x, URStr);
                    continue;
                }
                Token::LiteralUURString(x) => {
                    tok = str_literal!(x, UURStr);
                    continue;
                }
                Token::LiteralU8RString(x) => {
                    tok = str_literal!(x, U8RStr);
                    continue;
                }
                Token::LiteralStringUD(mut x) => {
                    tok = str_literal_ud!(x, StrUD);
                    continue;
                }
                Token::LiteralLStringUD(mut x) => {
                    tok = str_literal_ud!(x, LStrUD);
                    continue;
                }
                Token::LiteralUStringUD(mut x) => {
                    tok = str_literal_ud!(x, UStrUD);
                    continue;
                }
                Token::LiteralUUStringUD(mut x) => {
                    tok = str_literal_ud!(x, UUStrUD);
                    continue;
                }
                Token::LiteralU8StringUD(mut x) => {
                    tok = str_literal_ud!(x, U8StrUD);
                    continue;
                }
                Token::LiteralRStringUD(mut x) => {
                    tok = str_literal_ud!(x, RStrUD);
                    continue;
                }
                Token::LiteralLRStringUD(mut x) => {
                    tok = str_literal_ud!(x, LRStrUD);
                    continue;
                }
                Token::LiteralURStringUD(mut x) => {
                    tok = str_literal_ud!(x, URStrUD);
                    continue;
                }
                Token::LiteralUURStringUD(mut x) => {
                    tok = str_literal_ud!(x, UURStrUD);
                    continue;
                }
                Token::LiteralU8RStringUD(mut x) => {
                    tok = str_literal_ud!(x, U8RStrUD);
                    continue;
                }
                Token::Nullptr => {
                    self.operands.push(ExprNode::Nullptr(Box::new(Nullptr {})));
                    self.last = LastKind::Operand;
                }
                Token::This => {
                    self.operands.push(ExprNode::This(Box::new(This {})));
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
                    let dsp = DeclSpecifierParser::new(self.lexer);
                    let (tk, (_, typ, _, _)) = dsp.parse(Some(tok), None, context)?;

                    if let Some(typ) = typ {
                        self.operands.push(ExprNode::Type(Box::new(typ)));
                        self.last = LastKind::Operand;
                        tok = tk.unwrap_or_else(|| self.lexer.next_useful());
                        continue;
                    } else {
                        return Ok((tk, self.get_node()));
                    }
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::{preprocessor::context::DefaultContext, Lexer};
    use crate::parser::names::Qualified;
    use crate::parser::types::{BaseType, CVQualifier, Primitive, Type};
    use pretty_assertions::assert_eq;

    #[test]
    fn test_add_associativity_lr() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a + b + c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(BinaryOp {
                op: Operator::Add,
                arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
            }),
            arg2: ExprNode::Variable(Box::new(mk_var!("c"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_add_associativity_rl() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a = b = c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Assign,
            arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Assign,
                arg1: ExprNode::Variable(Box::new(mk_var!("b"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("c"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_priority() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a + b * c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Mul,
                arg1: ExprNode::Variable(Box::new(mk_var!("b"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("c"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_priority_2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a * b + c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(BinaryOp {
                op: Operator::Mul,
                arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
            }),
            arg2: ExprNode::Variable(Box::new(mk_var!("c"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_call() {
        let mut lexer = Lexer::<DefaultContext>::new(b"foo::bar(a, b)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(CallExpr {
            callee: ExprNode::Variable(Box::new(mk_var!("foo", "bar"))),
            params: vec![
                ExprNode::Variable(Box::new(mk_var!("a"))),
                ExprNode::Variable(Box::new(mk_var!("b"))),
            ],
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_sizeof() {
        let mut lexer = Lexer::<DefaultContext>::new(b"sizeof(A)");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::Sizeof,
            arg: ExprNode::Variable(Box::new(mk_var!("A"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_array() {
        let mut lexer = Lexer::<DefaultContext>::new(b"abc[x]");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Subscript,
            arg1: ExprNode::Variable(Box::new(mk_var!("abc"))),
            arg2: ExprNode::Variable(Box::new(mk_var!("x"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_array1() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a[b[x]]");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Subscript,
            arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Subscript,
                arg1: ExprNode::Variable(Box::new(mk_var!("b"))),
                arg2: ExprNode::Variable(Box::new(mk_var!("x"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_array2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a[b[c[x]]]");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Subscript,
            arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Subscript,
                arg1: ExprNode::Variable(Box::new(mk_var!("b"))),
                arg2: node!(BinaryOp {
                    op: Operator::Subscript,
                    arg1: ExprNode::Variable(Box::new(mk_var!("c"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("x"))),
                }),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_array3() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a[b[c[d[x]]]]");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Subscript,
            arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
            arg2: node!(BinaryOp {
                op: Operator::Subscript,
                arg1: ExprNode::Variable(Box::new(mk_var!("b"))),
                arg2: node!(BinaryOp {
                    op: Operator::Subscript,
                    arg1: ExprNode::Variable(Box::new(mk_var!("c"))),
                    arg2: node!(BinaryOp {
                        op: Operator::Subscript,
                        arg1: ExprNode::Variable(Box::new(mk_var!("d"))),
                        arg2: ExprNode::Variable(Box::new(mk_var!("x"))),
                    }),
                }),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_arrow_plus() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a->b(c) + d");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(BinaryOp {
            op: Operator::Add,
            arg1: node!(CallExpr {
                callee: node!(BinaryOp {
                    op: Operator::Arrow,
                    arg1: ExprNode::Variable(Box::new(mk_var!("a"))),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                }),
                params: vec![ExprNode::Variable(Box::new(mk_var!("c"))),],
            }),
            arg2: ExprNode::Variable(Box::new(mk_var!("d"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_pre_post_inc() {
        let mut lexer = Lexer::<DefaultContext>::new(b"++a++");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::PreInc,
            arg: node!(UnaryOp {
                op: Operator::PostInc,
                arg: ExprNode::Variable(Box::new(mk_var!("a"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_ind_post_inc() {
        let mut lexer = Lexer::<DefaultContext>::new(b"*p++");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(UnaryOp {
            op: Operator::Indirection,
            arg: node!(UnaryOp {
                op: Operator::PostInc,
                arg: ExprNode::Variable(Box::new(mk_var!("p"))),
            }),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_question_1() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a ? b : c");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(Conditional {
            condition: ExprNode::Variable(Box::new(mk_var!("a"))),
            left: ExprNode::Variable(Box::new(mk_var!("b"))),
            right: ExprNode::Variable(Box::new(mk_var!("c"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_question_2() {
        let mut lexer = Lexer::<DefaultContext>::new(b"a ? (void)b,c : d");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(Conditional {
            condition: ExprNode::Variable(Box::new(mk_var!("a"))),
            left: node!(BinaryOp {
                op: Operator::Comma,
                arg1: node!(BinaryOp {
                    op: Operator::Cast,
                    arg1: ExprNode::Type(Box::new(Type {
                        base: BaseType::Primitive(Primitive::Void),
                        cv: CVQualifier::empty(),
                        pointers: None,
                    })),
                    arg2: ExprNode::Variable(Box::new(mk_var!("b"))),
                }),
                arg2: ExprNode::Variable(Box::new(mk_var!("c"))),
            }),
            right: ExprNode::Variable(Box::new(mk_var!("d"))),
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_concat_string() {
        let mut lexer =
            Lexer::<DefaultContext>::new(b"\"abcde\"   \"fghijkl\" L\"mn\" R\"(opqrs)\"");
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(Str {
            value: StrLiteral::Str("abcdefghijklmnopqrs".to_string())
        });

        assert_eq!(node, expected);
    }

    #[test]
    fn test_concat_string_ud() {
        let mut lexer = Lexer::<DefaultContext>::new(
            b"\"abcde\"_foo   \"fghijkl\"_foo L\"mn\"_foo R\"(opqrs)\"_foo",
        );
        let mut parser = ExpressionParser::new(&mut lexer, Token::Eof);
        let mut context = Context::default();
        let node = parser.parse(None, &mut context).unwrap().1.unwrap();

        let expected = node!(Str {
            value: StrLiteral::StrUD(Box::new((
                "abcdefghijklmnopqrs".to_string(),
                "_foo".to_string()
            ))),
        });

        assert_eq!(node, expected);
    }
}
